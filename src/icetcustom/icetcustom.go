package icetcustom

import (
	"go/ast"
	"icetTerm"
)

type CustomParser interface {
	ParseSend(string, []ast.Expr, string, icetTerm.IDType, func(ast.Node) string) (bool, *icetTerm.Send)
	ParseReceive(string, []ast.Expr, string, string, string, func(ast.Node) string) (bool, *icetTerm.Recv)
}

// default implementation
type DefaultParser struct{}

func (d *DefaultParser) ParseSend(string, []ast.Expr, string, icetTerm.IDType, func(ast.Node) string) (bool, *icetTerm.Send) {
	return false, nil
}

func (d *DefaultParser) ParseReceive(string, []ast.Expr, string, string, string, func(ast.Node) string) (bool, *icetTerm.Recv) {
	return false, nil
}
