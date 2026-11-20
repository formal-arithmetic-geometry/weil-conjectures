# A0

Case: Slow Derived Tensor  
Variant: original `abbrev` declarations  
Commit: `bdab171985a`  
Lean/Mathlib: v4.33.1 / `0df444a360eaa60ab8c11dca51a86af692955474`  
Operation: final inferred-type/declaration `Kernel.isDefEq`  
Left/right: the `tensorObj` pair in `probes/KernelProbe.lean`  
Time: 49,867 ms forward; 50,279 ms reverse; full consumer 131,963/121,742 ms  
Representation: `def/abbrev`; same outer tensor head, different derived monoidal arguments  
Interpretation: supports H1; deep additive unfolds are downstream evidence  
Confidence: confirmed phase, strongly supported mechanism

The numeric values above are historical first-pass notes. Fresh round-two values are in
`A0-round2.md`, with source under `probes/round2/A1.lean`.
