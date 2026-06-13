The paper contains links into the Agda sources which it expects in `html/`.
Each invocation of `\agdaref{File}[Submodule]{identifier}` does two things:

1. It adds a checkmark into the text that links to `html/File.html#[Submodule.]identifier`.
2. It adds a reference to `identifier` to the generated file `References.agda`.
   Checking `References.agda` with Agda is a means to ensure that all links are valid in the sense that they point to an existing definition.

The `\agdaref` logic and implementation is due to Jean-Philippe Bernardy.
