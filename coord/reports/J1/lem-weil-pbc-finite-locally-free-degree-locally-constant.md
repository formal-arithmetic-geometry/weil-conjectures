## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant` states
`AlgebraicGeometry.finiteLocallyFree_fiberDimension_isLocallyConstant`.
It binds schemes `X S`, a morphism `f : X ⟶ S`, and the hypothesis
`[f.IsFiniteLocallyFree]`, which is exactly finite, flat, and locally of finite
presentation from `def-pc-finite-locally-free`. The let-bound function `δ` is the
fibre dimension `finrankΓ` of `f.fiberToSpecResidueField s`; this is the dimension
of `Γ(Y_s, O_{Y_s})` over `κ(s)`, using `Scheme.Hom.fiber` and
`Scheme.residueField`. The first conjunct says every fibre module is finite via
`Module.Finite`. The second says `δ` is locally constant. The third records that
each fibre `δ ⁻¹' {d}` is clopen. The final conjunct supplies the equivalent
open-and-closed decomposition: `U d` has exactly the points where `δ = d`, and
the restricted morphism `f ∣_ U d` has finite locally free degree `d`.

The theorem proof is `sorry`, as required at stage 2. Its proof docstring records
three source steps: apply the finite-flat rank lemma and identify fibre dimension;
take clopen rank fibres and restrict the morphism; identify these with the stated
`δ` decomposition.

Dependencies used: `def-pc-finite-locally-free` (source declaration
`AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` in
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`),
`def-weil-residue-field` (`AlgebraicGeometry.Scheme.residueField` from
`Mathlib.AlgebraicGeometry.ResidueField`), and `def-pc-fibre-product`
(`CategoryTheory.Limits.pullback` with the scheme pullback instance). The
recorded `lem-weil-pbc-finite-flat-rank-iso` is a proof dependency only; its
Mathlib leaves are `Scheme.Hom.isLocallyConstant_finrank`,
`finrank_of_isPullback`, and `isIso_iff_finrank_eq`.

Edge cases checked: `d = 0` is allowed; the fibre index is not assumed nonempty;
finite morphisms can have empty fibres, and `Module.Finite`/`finrankΓ` still
state the finite zero-dimensional case. No characteristic or nonemptiness
hypothesis is added, and the universe is explicit.

Searches made: `msearch.py ... leanfinder "finite locally free scheme morphism fibre
 dimension locally constant"` returned Mathlib finite-fibre and locally-constant
rank declarations but no exact scheme theorem; `msearch.py ... loogle
"Scheme.Hom.IsFiniteLocallyFree, Scheme.Hom.finrankΓ, IsLocallyConstant"` returned
no hit because the source declarations are outside Mathlib; `msearch.py ... grep
"fiberDegree.*finrankΓ|IsFiniteLocallyFree" Mathlib/AlgebraicGeometry` returned
no direct match. Repository grep found only the source finite-locally-free
classes and no theorem for this node. The node's existing LeanSearch/Loogle/
LeanFinder/grep records were also checked; they likewise identify only the
rank API, not this exact statement.

## Earlier second reading (a previous round; superseded)

I reread the node and module side by side. The explicit `[f.IsFiniteLocallyFree]`
hypothesis renders “finite, flat and locally of finite presentation”; `δ` renders
the residue-field dimension of the structure-ring sections of each fibre. The four
conjuncts render respectively finite-dimensional fibres, local constancy, clopen
rank fibres, and the indexed decomposition with exact fibres and degree-`d`
restricted morphisms. The source declarations used for finite locally free,
residue fields, fibre products, and restriction were checked at their recorded
locations. No hypothesis, characteristic, or nonemptiness condition was added.

## Second reading by J1

I read the node statement and the theorem signature item by item. The node introduces a
finite locally free morphism `f : Y → X`, with finite, flat, and locally finitely presented
hypotheses, a point `x : X`, its residue field `κ(x)`, the fibre `Y_x`, and
`δ_f(x) = dim_{κ(x)} Γ(Y_x, O_{Y_x})`. The Lean binders
`{X S : Scheme.{u}}`, `(f : X ⟶ S)`, and `[f.IsFiniteLocallyFree]` render exactly these
objects and hypotheses (with the source/target names interchanged harmlessly). The class
`Scheme.Hom.IsFiniteLocallyFree` was checked in `FiberDegree.lean` and extends precisely
`IsFinite`, `Flat`, and `LocallyOfFinitePresentation`.

The let binding
`δ : S → ℕ := fun s => (f.fiberToSpecResidueField s).finrankΓ` renders the residue-field
dimension of global sections of the scheme-theoretic fibre; `fiberToSpecResidueField` and
`finrankΓ` were checked in the recorded dependency source. The first conjunct
`∀ s, Module.Finite (S.residueField s) Γ(f.fiber s, ⊤)` renders finiteness of every
`δ_f(s)`. The second conjunct `IsLocallyConstant δ` renders local constancy on the
underlying topological space. The third conjunct
`∀ d, IsClopen (δ ⁻¹' {d})` renders that every rank level is open and closed. The final
existential supplies `U : ℕ → S.Opens`; its biconditional says each `U d` is exactly the
level set `δ ⁻¹' {d}`, and the class witness
`(f ∣_ U d).IsFiniteLocallyFreeOfDegree d` renders the restriction over that clopen piece
as finite locally free of degree `d`. Since the level-set equality gives pairwise
 disjointness and coverage, this is the node's coproduct decomposition. The trailing `True`
is propositionally harmless and the existential is equivalent to supplying the class
witness itself.

Edge cases were checked: `d = 0` is included by `d : ℕ`; empty level sets and empty fibres
are allowed; the zero-dimensional fibre is covered by `Module.Finite`; no characteristic,
nonemptiness, or reducedness assumption is introduced; and the single universe `u` applies
to both schemes and residue-field constructions, so no cases are excluded.

I searched the project source, Mathlib, and the local `lean/Sheaf` tree (including the
LeanSearch/Loogle/LeanFinder searches recorded in the worker report). The only related
API is the generic stalk-rank/local-constancy API; no existing declaration states this
fibre-dimension theorem. The recorded dependencies were checked: finite locally free is
`Scheme.Hom.IsFiniteLocallyFree`, residue fields are `Scheme.residueField`, and fibres are
the recorded pullback construction. No mismatch was found and no source or Lean change was
needed beyond recording the compiled declaration in the node's `lean` field.

## Reviewer fix (R-fdl1025)

The last conjunct `∀ d, ∃ _h : (f ∣_ U d).IsFiniteLocallyFreeOfDegree d, True` was replaced by the
equivalent `∀ d, (f ∣_ U d).IsFiniteLocallyFreeOfDegree d` (the class is a `Prop`). `δ` via
`finrankΓ (f.fiberToSpecResidueField s)` is `rfl`-equal to the recorded `f.fiberDegree s`, and the
`Module.Finite` conjunct uses the upstream `Scheme.Hom.fiberAlgebra` (checked by `rfl`). Upstream
FiberDegree.lean has no locally-constant fibre-degree lemma (only Mathlib's
`Scheme.Hom.isLocallyConstant_finrank` and `Scheme.Hom.finrank_eq_fiberDegree`, a proof route), so
the record stays `existing: false`.
