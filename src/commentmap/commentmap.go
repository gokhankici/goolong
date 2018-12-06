package commentmap

import (
	"go/ast"
)

type RelPos int

const (
	Before RelPos = iota
	After         = iota
)

type Comment struct {
	Comment string
	Pos     RelPos
}

type CMapVisitor struct {
	Node2Comment map[ast.Node][]Comment
	Comment2Node map[*ast.CommentGroup]ast.Node
	Comments     ast.CommentMap
}

func MakeCMapVisitor(comments ast.CommentMap) *CMapVisitor {
	// Mapping nodes to comments s.t. each comment is associated with at most one node.
	v := &CMapVisitor{
		make(map[ast.Node][]Comment),
		make(map[*ast.CommentGroup]ast.Node),
		comments}
	return v
}

func (v *CMapVisitor) Visit(node ast.Node) (w ast.Visitor) {
	// map each comment to the most specific node it is associated with
	if node != nil {
		comments := v.Comments.Filter(node)
		for _, comment := range comments.Comments() {
			oldNode, exists := v.Comment2Node[comment]
			if !exists || isSubnode(node, oldNode) {
				v.Comment2Node[comment] = node
			}
		}
	}
	return v
}

func isSubnode(n ast.Node, m ast.Node) bool {
	return n.Pos() >= m.Pos() && n.End() <= m.End()
}

func (v *CMapVisitor) getRelativePosition(comment *ast.CommentGroup, node ast.Node) RelPos {
	var relPos RelPos
	if comment.Pos() <= node.Pos() {
		relPos = Before
	} else if comment.End() >= node.End() {
		relPos = After
	}
	return relPos
}

func (v *CMapVisitor) MapComments() {
	for comment, node := range v.Comment2Node {
		comments, exists := v.Node2Comment[node]
		if !exists {
			comments = make([]Comment, 0)
		}
		relPos := v.getRelativePosition(comment, node)
		comments = append(comments, Comment{Comment: comment.Text(), Pos: relPos})
		v.Node2Comment[node] = comments
	}
}
