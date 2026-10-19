## Worker report

This repair supplies the missing stage-2 statement module
`Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange`.  It declares
`AlgebraicGeometry.geometricReduced_fibre_locus_baseChange`; its proof is the
single permitted `sorry`.  The module imports the recorded base-change interface
`WeilConjectures.AlgebraicGeometry.BaseChangeConventions` and Mathlib's reduced
scheme predicate.  The original node statement, source, dependencies, and proof
plan are unchanged.

The Lean signature renders each clause as follows.  `X`, `T`, and `T'` are
`Scheme.{u}`, and `f : X ⟶ T`, `g : T' ⟶ T` are arbitrary scheme morphisms.
The base changed morphism is `pullback.snd f g : pullback f g ⟶ T'`, while the
original morphism is `f`.  For each `t' : T'`, every chosen algebraic closure is
represented by `(Ω : Type u) [Field Ω] [Algebra (T'.residueField t') Ω]
[IsAlgClosure (T'.residueField t') Ω]`; its geometric fibre is the displayed
pullback along `Spec.map (CommRingCat.ofHom (algebraMap ...)) ≫
T'.fromSpecResidueField t'`.  Reducedness is Mathlib's `IsReduced`, exactly the
local-ring/no-nilpotent notion recorded by `def-pc-reduced-scheme`.  The left set
is therefore `{t' | ∀ Ω, IsReduced (X'_{\bar t'})}`.  The right set is the
preimage `g ⁻¹' {t | ∀ Ω, IsReduced (X_{\bar t})}` with the analogous residue
field, closure, and pullback expression over `T`.  The outer equality is equality
of subsets of `T'`; no flatness, finite-presentation, or surjectivity binder is
present, and empty fibres are included.

The dependency declarations used are `AlgebraicGeometry.Scheme` and
`Scheme.Hom` from Mathlib's `AlgebraicGeometry.Scheme`; the base-change record's
`pullback` conventions and `AlgebraicGeometry.baseChange_fiber`/
`Scheme.Hom.geometricFiberAt` from `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`;
`CategoryTheory.Limits.pullback` from
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; `Field`, `Algebra`,
`IsAlgClosure`, `Spec.map`, `CommRingCat.ofHom`, `Scheme.fromSpecResidueField`,
and `AlgebraicGeometry.IsReduced` from their Mathlib declarations.  The statement
uses the canonical geometric-fibre pullback directly, so it does not introduce a
private fibre definition.

Edge cases checked: identity base change gives the same fibre locus; arbitrary
morphisms remain allowed; an empty fibre is reduced vacuously by the local-ring
definition; and all characteristics and both separable and inseparable residue
field extensions remain quantified.  The universe `u` is shared by schemes and
chosen closure fields exactly as in the recorded geometric-fibre interface.

Searches for an existing declaration were made with `msearch.py` leanfinder
("reduced geometric fibre locus commutes with arbitrary scheme base change"),
loogle (`GeometricallyReduced`, `IsReduced`, `fiber`), and grep over Mathlib's
`AlgebraicGeometry` directory (`GeometricallyReduced|geometricallyReduced|0576`).
They found only global geometric-reducedness stability and ring criteria, not this
pointwise locus equality.  `rg` over the upstream `WeilConjectures` source and
project `lean/Sheaf` for `geometricReduced_fibre_locus_baseChange`, the node id,
and `reduced.*fibre.*base` found no exact declaration.  The Stacks source read was
More on Morphisms, Tag 0576, with Varieties Tags 035X and 020I for the geometric
reducedness formulation.  No statement correction, new node, dependency repair,
or `STATEMENT-DISPUTED` finding is present.

## Second reading by Q37

I reread the node, its four statement dependencies, the complete theorem header,
and the source interface.  The morphisms and schemes have no added hypotheses; the
base-changed map is `pullback.snd f g`; both sides quantify chosen algebraic
closures and apply `IsReduced` to the corresponding geometric-fibre pullback.
The inverse-image notation and point variables have the exact directions in the
node.  The signature has no finite-presentation, flatness, surjectivity, or
nonemptiness assumptions, and the proof is only `sorry`.  No mismatch was found.

Validation: `scompile.py Q37 lem-trf-geometric-reduced-fibre-locus-base-change
lean/Sheaf/TraceFormula/GeometricReducedFibreLocusBaseChange.lean` compiled both
sandbox and library overlays cleanly with no warnings.
