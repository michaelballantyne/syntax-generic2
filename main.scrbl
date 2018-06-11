#lang scribble/manual

@title{Syntax Generics}

@defmodule[syntax-generic2]

@defform[(define-generic-syntax generic-name
           fallback fallback-procedure)]{
  Defines a syntax generic procedure.
}

@defform[(define-syntax/generics name
           expand-procedure
           [generic-name generic-procedure] ...)]{
  Defines a syntactic form with a macro transformer and syntax generic implementations.
}

@defform[(syntax-generic-prop generic-name)]{
  Evaluates to the structure type property associated with a syntax generic.
}
