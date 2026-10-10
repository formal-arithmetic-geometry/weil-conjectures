# Stage 1 report

1. Files written: the item `lem-pc-zero-scheme-properties`; new closed declaration nodes `lem-pc-zero-scheme-locally-principal`, `lem-pc-zero-scheme-ideal-local`, `lem-pc-zero-scheme-pullback`, and `lem-pc-zero-scheme-zero-iff`. All four are slopmaster2 closed declarations; none is a Mathlib leaf.
2. Attachments: `AlgebraicGeometry.Scheme.Modules.Hom.isLocallyPrincipal_zeroLocus` belongs to `lem-pc-zero-scheme-locally-principal`; `AlgebraicGeometry.Scheme.Modules.Hom.ideal_zeroLocus` belongs to `lem-pc-zero-scheme-ideal-local`; `AlgebraicGeometry.Scheme.Modules.Hom.comap_zeroLocus` belongs to `lem-pc-zero-scheme-pullback`; `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus_eq_bot_iff` belongs to `lem-pc-zero-scheme-zero-iff`.
3. No WANTED documents.
4. The imported proof used an under-specified dual-pullback argument and cited nodes whose statements did not provide the exact local theorem. I replaced it with the four exact general morphism declarations in `Modules/ZeroLocus.lean`, then specialized to the section morphism. The item itself has no exact sorry-free declaration because its audit declaration is a different Picard existence theorem resting on sorry.
## Review by C1

I read the item source and the complete theorem blocks at lines 491-576 of `ZeroLocus.lean`. Step 1 uses the locally-principal theorem and the affine ideal theorem exactly as quoted; the section is represented by `O_X -> M`. Step 2 uses the pullback equality, which is stated for arbitrary morphisms, so it covers the flat case. Step 3 uses the zero-locus/bottom iff theorem and the canonical section-morphism correspondence. I searched Mathlib with LeanFinder, Loogle, and source grep for each new declaration; only lower-level primitives or a set-level preimage theorem appeared, so all four remain closed attached nodes. Small cases checked: `M=N=O_X` reduces to a principal ideal `(a)`, and `a=0` gives the whole scheme.

## Second reading by C1

- Item statement: checked against the blueprint and defining zero-scheme nodes; all three clauses, the flatness hypothesis, and the affine equation agree.
- Step 1: checked against `Hom.isLocallyPrincipal_zeroLocus` and `Hom.ideal_zeroLocus` in `ZeroLocus.lean` lines 491–500 and 570–576; both cited statements provide the claimed local conclusions.
- Step 2: checked against `Hom.comap_zeroLocus` in lines 502–533; its arbitrary-morphism statement implies the stated flat case.
- Step 3: checked against `Hom.zeroLocus_eq_bot_iff` in lines 539–568; the lattice bottom is the whole closed subscheme, matching `Z(s)=X`.
- `lem-pc-zero-scheme-locally-principal`: source hypotheses and conclusion checked; both modules and the morphism are explicit and TeX-formatted.
- `lem-pc-zero-scheme-ideal-local`: source affine-generator hypotheses checked; `U=Spec(A)`, the coefficient, and principal ideal are explicit and TeX-formatted.
- `lem-pc-zero-scheme-pullback`: source equality checked; both schemes, modules, morphism, and pullback are explicit.
- `lem-pc-zero-scheme-zero-iff`: source theorem checked; both modules and the morphism are explicit, with the source's `\\bot` convention.
- Existing-node and Mathlib searches in `searches.jsonl` found no exact duplicate or Mathlib theorem; all four declarations are closed and sorry-free in slopmaster2.
- Small cases checked: `b=0` gives the whole scheme, a nonzero coefficient over a field gives the expected principal zero scheme, and the empty scheme is vacuous; no dimension parameter occurs, so `n=0,1` are irrelevant.
- Changes: tightened all four new statements for self-contained TeX notation and explicit objects, and updated citation quotes verbatim; proof steps and mathematical claims were unchanged.
