## Worker report

The module `Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion` states
`AlgebraicGeometry.affine_torAmplitude_iff`, with `sorry` as its only proof.
It states part (1) of Stacks Tag 08E9; no definitions or extra theorems are introduced.

Hypotheses and clauses:
- A ring A and X = Spec(A): `(A : Type u) [CommRing A]` and `Spec (.of A)`.
  Commutativity is the convention for rings in the scheme source.
- An arbitrary complex of A-modules: `M : CochainComplex (ModuleCat.{u} A) ℤ`.
- E in D_QCoh(O_X): `E : schemeDerivedQCohCategory (Spec (.of A))`.
  Its underlying derived object is `E.obj`.
- Correspondence under the affine equivalence: `hE` is an isomorphism between
  `DerivedCategory.Q.obj` of the termwise tilde complex of M and `E.obj`.
  The recorded affine-equivalence theorem identifies exactly this composite with
  its equivalence functor on Q M. Thus the hypothesis specifies the correspondence,
  rather than postulating an arbitrary unrelated equivalence. Using an isomorphism
  permits every choice of corresponding E.
- Integers a ≤ b: `(a b : ℤ) (hab : a ≤ b)`.
- Clause (i), every O_X-module G: the universal binder over
  `SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)` has no
  quasi-coherence, finiteness, or flatness restriction.
- Clause (i), every degree outside [a,b]: `∀ i : ℤ, i < a ∨ b < i → ...`.
  Its vanishing assertion is the shared `schemeDerivedTensorCohomologyVanishes`
  applied to `Spec (.of A)`, `E.obj`, G and i.
- Clause (ii): `DerivedCategory.torAmplitudeIn (ModuleCat.{u} A) a b
  (DerivedCategory.Q.obj M)`. Its full source definition universally quantifies over
  every module N, tensors with N in degree zero, and requires homology concentrated
  in [a,b]. Its derived monoidal structure is the source's canonical derived tensor.
- Equivalence of (i) and (ii): `↔`, with the same a,b on both sides.
- The two `HasDerivedCategory` binders select localizations for the two abelian
  categories, with independently explicit morphism universes wA,wX. They are
  foundational structure, not mathematical boundedness or existence restrictions.

Dependencies read and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`, with their signatures and docstrings; the statement uses Spec.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`.
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`:
  `exists_affineQCohDerivedEquivalence`. Its full signature and proof docstring were
  read. Its natural isomorphism identifies Q followed by the affine equivalence and
  inclusion with termwise tilde followed by Q; the latter is used explicitly in hE.
- `Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes`:
  `schemeDerivedTensorCohomologyVanishes`. The already landed definition node
  `def-pc-derived-tensor-cohomology-vanishes` is added to stmt_deps to record this use.
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`:
  `DerivedCategory.torAmplitudeIn`, definition and docstring read in full.
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`
  and `Mathlib.RingTheory.Flat.CategoryTheory` supply canonical derived tensor
  instances on modules, as in the landed module Tor-amplitude flat-model statement.

Edge cases checked: A can be the zero ring, so Spec A may be empty; no Nontrivial
or nonempty hypothesis is imposed. M and E can be zero. No boundedness,
Noetherianity, or finite generation is assumed. Negative endpoints and a=b are
included, with vanishing only strictly outside the interval. Test modules are
arbitrary objects in the same universe as A, consistently with the source's
ModuleCat Tor predicate and the project's scheme module carrier. No additional
independent smaller test universe is used. All variables and universes are explicit.

Searches for an existing statement (2026-10-11 UTC):
- msearch leanfinder: "A complex of modules over a commutative ring has Tor amplitude
  a b if and only if its associated sheaf complex on Spec has Tor amplitude a b".
  Eight hits on derived-category IsGE/IsLE and homology concentration, no affine
  Tor-amplitude comparison.
- msearch loogle: `AlgebraicGeometry.Scheme, DerivedCategory`: zero hits.
- msearch grep: `torAmplitudeIn|tor_amplitude|TorAmplitude`, Mathlib
  AlgebraicGeometry: zero hits.
- msearch leansearch: "Tor amplitude of associated sheaf complex on affine scheme":
  unavailable, Internal Server Error; no conclusion drawn from this service.
- rg in WeilConjectures and lean/Sheaf for `torAmplitudeIn` and affine/Tor terms
  found the general ring predicate, its flat-model theorem and étale/pro-étale
  analogues. No existing declaration states this scheme-module comparison.
- rg in WeilConjectures for the exact item id: no hits.
- rg in lean/Sheaf and WeilConjectures/AlgebraicGeometry for
  `affine.*torAmplitude|torAmplitude.*affine`: no hits.
- rg for `affine_torAmplitude_iff` in dag/lean_names_upstream.json, Mathlib,
  WeilConjectures, and lean/Sheaf: no existing declaration with that name.

The source was read in the available local Stacks text
`/home/ubuntu/c1-stacks-review/perfect.tex`, label
`lemma-tor-dimension-affine`, including its full proof. The repository's
literature/stacks-project checkout is absent on this machine; this available copy
contains exactly the cited affine equivalence and Tor-amplitude statement.
No statement correction or dispute is needed. The source label in the item's
source record says lemma-tor-amplitude-affine, while the text's label is
lemma-tor-dimension-affine; the mathematical statement and Tag 08E9 are correct.

Validation: scompile compiled the module on the server in 5.0 seconds, exit code
0, with no warnings. The delivery dry run is the final mechanical check; the
independent second reader must supply the second-reading section and deliver.

## Second reading by F1

I reread the node `dag/nodes/sec-picard-framework/lem-pc-affine-tor-amplitude-criterion.json`, its
statement, dependencies, and the source at `/home/ubuntu/c1-stacks-review/perfect.tex`, label
`lemma-tor-dimension-affine` (Tag 08E9), part (1). The source introduces an affine ring `A`,
`X = Spec(A)`, an arbitrary complex `M` of `A`-modules, and its corresponding derived object
`E`; for integers `a ≤ b` it asserts the equivalence between sheaf Tor-amplitude tested against
every `O_X`-module in every degree outside `[a,b]`, and module Tor-amplitude tested against every
`A`-module. The source imposes no Noetherian, finiteness, nonzero-ring, or nonempty-scheme
hypothesis.

The Lean renders these items as follows. `(A : Type u) [CommRing A]` and
`Spec (.of A)` give the ring and affine scheme. `M : CochainComplex (ModuleCat.{u} A)` is the
arbitrary module complex. `E : schemeDerivedQCohCategory (Spec (.of A))` is the
quasi-coherent derived object, and `hE : Nonempty (...)` identifies `E.obj` with the derived
termwise-tilde image of `M`. `(a b : ℤ) (hab : a ≤ b)` gives the interval. The left clause
quantifies over every `G : SheafOfModules (moduleRings ... )` and every `i : ℤ` with
`i < a ∨ b < i`, and applies the shared predicate
`schemeDerivedTensorCohomologyVanishes (Spec (.of A)) E.obj G i`. The right clause is exactly
`DerivedCategory.torAmplitudeIn (ModuleCat.{u} A) a b (DerivedCategory.Q.obj M)`, whose
recorded definition tests every module object via derived tensor with degree-zero placement and
homology concentration. The final connective is `↔`, preserving the node's quantifier order.
The explicit `HasDerivedCategory.{wA}` and `HasDerivedCategory.{wX}` binders are category
localization structure, not extra mathematical assumptions.

Edge cases are included: the zero ring and empty `Spec`, zero `M` or `E`, negative endpoints,
`a = b`, and all integer degrees. No Noetherianity, finite generation, boundedness, or
characteristic assumption is added; all module and sheaf universes are shared with `A`.

I independently searched the local Mathlib and project source with `rg` for
`affine_torAmplitude_iff`, affine Tor-amplitude comparisons, and `torAmplitudeIn`; only the
general `DerivedCategory.torAmplitudeIn` and unrelated Fourier/étale uses were found. The
worker's LeanFinder, Loogle, grep, and LeanSearch records in `searches.jsonl` likewise found no
existing affine criterion. I read the dependency declarations for the affine QCoh equivalence,
the derived-category carrier, the shared tensor-cohomology-vanishing predicate, and the module
Tor-amplitude definition. They match the dependency nodes and are used directly. No mismatch was
found, so no Lean, node, or dependency repair was needed. The module compiles cleanly with only
its intentional theorem `sorry`.
