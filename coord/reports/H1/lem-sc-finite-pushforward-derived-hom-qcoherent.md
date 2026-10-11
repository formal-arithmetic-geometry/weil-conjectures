## Worker report

The module `Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent` states
`AlgebraicGeometry.finite_pushforward_derivedHom_qcoherent`, with one `sorry` proof.
It introduces no definitions, auxiliary theorems, new nodes or dependency modules.
The node statement and all its existing dependency edges are unchanged.

Hypothesis and clause correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`, covering arbitrary schemes in universe u.
- The finite morphism: `(f : X ⟶ Y) [IsFinite f]`.
- Noetherian source and target: `[IsNoetherian X] [IsNoetherian Y]`; neither is dropped.
- The specific algebra B = f_* O_X: `(B : Y.CommAlgebraSheaf)` and
  `hBf : B = Under.mk (⟨f.c⟩ : Y.sheaf ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf)`.
  This is an equality of sheaves of O_Y-algebras, so it fixes both the pushforward
  ring sheaf and its structure map. Quantifying over B with this equality is just
  naming the specified algebra, not assuming an arbitrary algebra has the conclusion.
- K in D^+_QCoh(Y): `(K : schemeDerivedQCohCategory Y)` supplies all-degree
  quasi-coherence; `(hK : ∃ n : ℤ, K.obj.IsGE n)` supplies a global lower bound.
- The `HasDerivedCategory` binders select the shared localizations for O_Y,
  its open-site restrictions (needed by IsPseudoCoherent), and B. They are the
  existing dependency signatures' infrastructure, not mathematical hypotheses
  such as projectivity, finite Tor dimension, separatedness or regularity.
- B is quasi-coherent: the conclusion begins `∃ hB : B.toModule.IsQuasicoherent`.
  This proof is needed by the existing algebra-valued derived-Hom definition.
  It is supplied in the conclusion, never assumed. The node already treats B as
  an input to the definition of D^+_QCoh of a quasi-coherent algebra.
- B is pseudo-coherent as an O_Y-module: `Scheme.IsPseudoCoherent Y
  ((DerivedCategory.singleFunctor ... 0).obj B.toModule)`. The module is placed
  in degree zero, as required for pseudo-coherence of the algebra as a module.
- The derived internal Hom with its natural B action: precisely
  `(derivedRHomAlgebraModule Y B hB).obj K.obj`, the recorded functor, not a
  separately chosen B-module structure or an unspecified object.
- Membership in D^+_QCoh(B): `sheafAlgebraDerivedQCohProperty Y B hB` of that
  exact object. This predicate includes both a global lower bound and
  quasi-coherence of every underlying cohomology O_Y-module.
- After forgetting the action: `(SheafOfModules.restrictScalars
  ((sheafCompose ... (forget₂ CommRingCat RingCat)).map B.hom)).mapDerivedCategory.obj`
  of the same algebra-valued derived-Hom object. `schemeDerivedQCohProperty Y`
  asserts all-degree quasi-coherence of this forgotten object; the final
  `∃ n : ℤ, (...).IsGE n` asserts its global lower bound.
  The recorded `derivedRHomAlgebraModule_underlying` identifies it with the
  recorded ordinary `derivedInternalHom`; no second RHom construction is used.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (schemes and their morphisms).
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`;
  its affine-preimage and finite-coordinate-ring signature matches finiteness.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`.
- `Sheaf.AlgebraicGeometry.PseudoCoherentComplex`: `Scheme.IsPseudoCoherent`;
  its full local finite-free-complex signature and docstring were read.
- `Sheaf.AlgebraicGeometry.DerivedCategoryQCoherentAlgebra`:
  `sheafAlgebraDerivedCategory`, `sheafAlgebraDerivedQCohProperty` (the latter
  expands to boundedness and `sheafAlgebraModuleIsQuasiCoherent`).
- `Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule`: `derivedRHomAlgebraModule`,
  `sheafAlgebraRestrictScalars_preservesFiniteLimits`,
  `sheafAlgebraRestrictScalars_preservesFiniteColimits`,
  `derivedRHomAlgebraModule_underlying`. The exactness instances support the
  shared `mapDerivedCategory` forgetful functor.
- `Sheaf.Algebra.Homology.DerivedInternalHom`: `CategoryTheory.derivedInternalHom`;
  its full signature and resolution construction were read. It is used through
  the recorded underlying-object comparison, rather than adding a redundant
  comparison-isomorphism clause to this node's conclusion.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsNoetherian`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.IsGE`,
  with `isGE_iff` confirming that this means vanishing of cohomology below n.

Edge cases checked before writing: empty schemes and the zero input complex give
zero complexes, which are pseudo-coherent / quasi-coherent and bounded below.
No nonemptiness or nonzero hypotheses appear. Arbitrary negative lower bounds are
allowed by ℤ. Singular Noetherian targets are included: B need not be perfect,
locally free or of finite projective dimension; no such hypotheses were added.
No characteristic restriction appears. Noetherian Y is quasi-compact, so the
local boundedness from Stacks 0A6H admits a uniform bound via a finite cover.
Universe parameters u, w, wB and every variable are explicit; the sheaf-module
carriers are the shared moduleRings carriers, not a second derived category
using the distinct category instance on Y.Modules.

Searches for existing statements (2026-10-11 UTC):

- msearch.py / leanfinder: "finite morphism Noetherian schemes pushforward
  structure sheaf pseudo coherent derived internal Hom bounded below quasi
  coherent". Eight hits: locally Noetherian ascent, finite-type module sheaves,
  pushforward and its adjoint, finite coordinate-ring maps, quasi-finiteness.
  No matching derived-Hom statement.
- msearch.py / loogle: "IsFinite, DerivedCategory". Zero hits, unknown
  identifier IsFinite in the service index.
- msearch.py / grep, Mathlib/AlgebraicGeometry:
  "derivedRHom|IsPseudoCoherent|pushforwardAlgebra". Zero hits.
- rg of WeilConjectures/AlgebraicGeometry for the item id, derivedRHom and
  IsPseudoCoherent: no hits. Searches of the project Lean found the dependency
  definitions, finite-duality citer, and existing finite/coherent pushforward
  lemmas, but no declaration of this complete statement.
- rg of `dag/lean_names_upstream.json`, project Lean and source Lean for the
  proposed full-name suffix `finite_pushforward_derivedHom_qcoherent`: no hits.
- The exact `Under.mk ⟨f.c⟩` algebra representation was checked against the
  already landed `affine_morphism_relative_spec`; it is written explicitly here
  without copying that module's file-local notation.

Source checked: [Stacks 0AX2](https://stacks.math.columbia.edu/tag/0AX2),
first assertion and proof, and [Stacks 0A6H](https://stacks.math.columbia.edu/tag/0A6H),
part (1). The local Stacks source is not present in this clone, so these official
source pages were opened. No statement fault or STATEMENT-DISPUTED flag.

Validation: local compilation initially found the recently landed
DerivedRHomAlgebraModule.olean missing from the refreshed local library; server
compilation was used as instructed for this situation. The server compiled the
78-line module cleanly in 8.2 seconds. deliver2.py --no-push printed OK: server
compile and preflight pass except for the independent second reading, which is
the next worker's task. Nothing was pushed.

## Second reading by H1

I independently opened the item node, its delivered module, and all seven
statement dependencies, including the recorded declarations and their source
modules. There are no new nodes, dependency modules, or statement corrections in
this delivery.

Source reading: I opened Stacks Tag 0AX2 (Lemma 48.11.4), including its proof,
and Tag 0A6H (Lemma 36.10.8). Tag 0AX2 assumes a finite pseudo-coherent
morphism (with finite morphisms of Noetherian schemes as the stated
specialization), and says that derived internal Hom from the finite pushforward
structure sheaf maps bounded-below quasi-coherent complexes to bounded-below
quasi-coherent complexes over the pushforward algebra. Tag 0A6H(1) supplies
quasi-coherence and local boundedness for Hom from a pseudo-coherent complex.
The node specializes to Noetherian X and Y and records the global lower bound
needed by its D-plus definitions; it adds no geometric hypothesis absent from
the source.

Object, hypothesis, and conclusion inventory, with the Lean match and verdict:

- Schemes and morphism: `{X Y : Scheme.{u}}` and `(f : X ⟶ Y)`. These are
  Mathlib's scheme and scheme-morphism objects, exactly the node's X, Y and f.
- Finiteness: `[IsFinite f]`, the recorded Mathlib declaration for
  `def-weil-finite-integral-morphism`; this is precisely finite, including the
  affine and finite-coordinate-ring conditions. Exact match.
- Noetherian hypotheses: `[IsNoetherian X] [IsNoetherian Y]`. Both schemes are
  Noetherian as required by the node; no separatedness, regularity, or
  characteristic assumption is present.
- Pushforward algebra: `(B : Y.CommAlgebraSheaf)` together with
  `hBf : B = Under.mk (⟨f.c⟩ : Y.sheaf ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf)`. This names
  exactly the sheaf algebra `f_* O_X`, including its O_Y-algebra structure,
  rather than allowing an unrelated B. Exact match.
- Derived-category infrastructure: the explicit `HasDerivedCategory` binders
  for O_Y, every open restriction used by pseudo-coherence, and B. These are
  the localization choices required by the recorded dependency declarations,
  not extra mathematical assumptions. Exact match.
- Input K in D-plus quasi-coherent: `(K : schemeDerivedQCohCategory Y)` and
  `(hK : ∃ n : ℤ, K.obj.IsGE n)`. The subtype supplies quasi-coherent
  cohomology and `IsGE` supplies one global lower bound, exactly D⁺_QCoh(Y).
- Quasi-coherence witness for B: `∃ hB : B.toModule.IsQuasicoherent`. The
  node calls B the pushforward algebra and the algebra-valued derived-Hom
  dependency requires this witness; it is concluded, never assumed.
- Pseudo-coherence: the first conjunct is
  `Scheme.IsPseudoCoherent Y ((DerivedCategory.singleFunctor ... 0).obj
  B.toModule)`, placing B in degree zero exactly as the node's
  pseudo-coherent O_Y-module clause requires.
- Derived Hom with B action: the second conjunct is
  `sheafAlgebraDerivedQCohProperty Y B hB
  ((derivedRHomAlgebraModule Y B hB).obj K.obj)`. This is the recorded
  natural B-module derived internal Hom and its D⁺_QCoh(B) membership, not a
  separate or weaker Hom construction.
- Forgetting the action: the final two conjuncts apply the recorded
  `SheafOfModules.restrictScalars ... B.hom` derived functor to that same
  object, assert `schemeDerivedQCohProperty Y`, and assert an existential
  integer lower bound. This is exactly the final D⁺_QCoh(Y) clause; the
  underlying comparison is the dependency theorem
  `derivedRHomAlgebraModule_underlying`.

Edge cases were checked: empty schemes, B = 0, and K = 0 are admitted; no
nonemptiness or positive-rank condition occurs. The lower bound may be any
integer, including zero or a negative integer. Singular Noetherian schemes and
all characteristics remain allowed. The universe `u` is shared by schemes,
sheaves, and the pushforward; `w` and `wB` only choose derived localizations,
so no scheme or index universe is accidentally excluded. Finite-free ranks in
the pseudo-coherence dependency include rank zero.

Independent searches were repeated with LeanFinder/Loogle and grep searches of
Mathlib, `WeilConjectures/`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
queries for finite pushforward, pseudo-coherent derived Hom, and
`finite_pushforward_derivedHom_qcoherent` found no existing declaration. The
only matches were the dependency definitions and unrelated affine or generic
quasi-coherence results. The source and dependency declarations were therefore
used as recorded; no duplicate notion was introduced.

No mismatch was found and no file was changed beyond this report. The theorem
has one `sorry` proof and no proved auxiliary assertion or hollow definition.
Its declaration docstring gives all three node proof steps and their cited
dependencies. The signature is copied verbatim into the node's `lean.statement`,
all variables and universes are explicit, and lines remain within the project
limit. `lcompile.py` succeeds with exit code 0.
