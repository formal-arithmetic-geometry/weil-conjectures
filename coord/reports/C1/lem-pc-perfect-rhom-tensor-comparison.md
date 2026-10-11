## Worker report

The module `Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison` states the perfect
RHom--tensor comparison. It binds a scheme `X`, the derived-category instances on `X`
and its opens, quasi-coherent complexes `K` and `M`, and the perfectness hypothesis on
`K`. The existential conclusion introduces `Kdual` with the specified derived internal
Hom definition, evaluation and coevaluation maps, their symmetry isomorphism, the
perfectness of `Kdual`, the tensor--RHom comparison map and its `IsIso` proof, the bidual
map and its `IsIso` proof, uniqueness of coevaluation under evaluation, and an
`ExactPairing`. The final clause quantifies every scheme morphism `g : T ⟶ X` and gives
the base-change map from `Lg* Kdual` to `RHom(Lg* K,O_T)` together with `IsIso`.
The two zig-zag identities are represented by the `ExactPairing` dependency (whose
class fields are exactly the two triangle identities); the explicit evaluation and
coevaluation maps are retained in the statement.

The hypotheses render as the explicit `HasDerivedCategory` instance on
`SheafOfModules (moduleRings X.toRingedSpace)` and the corresponding instance for every
open, followed by `K M : schemeDerivedQCohCategory X` and
`hK : Scheme.IsPerfect X K.obj`. The clauses render as the fields and maps listed above,
with all morphism types written in `schemeDerivedCategory` and all base-change data
quantified over `T` and `g`.

Dependency declarations used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` (Mathlib).
- `def-pc-perfect-complex`: `AlgebraicGeometry.Scheme.IsPerfect`,
  `Sheaf.AlgebraicGeometry.PerfectComplex`.
- `def-pc-derived-category`: `AlgebraicGeometry.schemeDerivedCategory`,
  `Sheaf.AlgebraicGeometry.DerivedCategory`.
- `def-pc-derived-pullback`: `AlgebraicGeometry.derivedPullback`,
  `Sheaf.AlgebraicGeometry.DerivedPullback`.
- `def-pur-derived-internal-hom`: `CategoryTheory.derivedInternalHom`,
  `Sheaf.Algebra.Homology.DerivedInternalHom`.
- `def-pc-tensor-complex-sheaves`: `HomologicalComplex.mapBifunctor` (Mathlib).
- `lem-sc-derived-internal-hom-adjunction`:
  `AlgebraicGeometry.scheme_derivedInternalHom_adjunction`,
  `Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction`.
- `lem-pc-derived-pullback-tensor-product`:
  `AlgebraicGeometry.derivedPullback_tensorProduct`,
  `Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct`.

Edge cases checked: `K` and `M` are arbitrary objects of the quasi-coherent derived
category (including zero objects); `T` and `g` are arbitrary, including identity and
empty schemes; no finiteness or nonemptiness assumptions are added, and universes are
shared explicitly by the scheme and coefficient categories.

Searches made: `msearch.py C1 lem-pc-perfect-rhom-tensor-comparison leanfinder
"perfect complex derived internal Hom tensor comparison"` (no matching declaration);
`msearch.py ... loogle "ExactPairing, derivedInternalHom, IsPerfect"` (only generic
`ExactPairing` and no scheme comparison); `msearch.py ... grep
"perfect.*rhom|derived.*internal.*hom.*tensor" Mathlib/` (no matching theorem);
`rg -n "perfect_rhom_tensor_comparison|RHom.*tensor"` in the project (no prior
statement). Existing dependency modules were inspected and imported directly.

## New nodes

`def-pc-derived-pullback-monoidal-model` provides the missing canonical monoidal model
for the recorded O_X-module derived pullback. The public predicate uses Mathlib
Functor.CoreMonoidal, pins the module functor to tensorPullback on objects and arrows,
pins its tensorator to module_pullback_tensor, pins the complex comparison by every
summand inclusion, and pins the derived tensorator by the K-flat counit square. Unit
laws determine the unit comparison. A named existence theorem carries the complete
K-flat descent argument, and the chosen model is a definition from that specified
existence theorem. Source: cohomology.tex, section-derived-pullback and 079U
lemma-pullback-tensor-product. The new-node statement lists these same data and equations;
its source imposes no flatness on g. Searches in its record include unavailable
LeanSearch, LeanFinder, and grep across all four trees; no existing canonical scheme
O_X-module model was found. It is a definition node in the item's chapter and unit,
with the ancestor and via chain required by the field rule. It is cited by the item.
The generic strong-monoidal notion is reused, not redefined. Both new definitions and
the existence theorem carry this new node's blueprint tag.

## Dependency modules

None.

## Second reading by C1

I independently read the node, all eight statement-dependency records and their Lean
signatures, and the actual dependency modules. The Stacks sources are not populated
under this read-only clone's literature directory; I read the local Stacks source
cohomology.tex at /home/ubuntu/c1-stacks-review/cohomology.tex, specifically
lemma-dual-perfect-complex (08DQ), lemma-internal-hom-evaluate-isom,
example-dual-derived (0FPC), lemma-pullback-internal-hom (0GM7),
section-derived-pullback and lemma-pullback-tensor-product (079U).
The sources assume arbitrary ringed spaces and arbitrary morphisms in the relevant
perfect-complex clauses: no Noetherian, boundedness of M, flatness of g, separatedness
or characteristic assumption. The node specializes this to schemes and QCoh M.
No natural-language statement correction was needed or made.

Object, hypothesis and conclusion checklist, with the repaired Lean open:

1. X is an arbitrary scheme: `(X : Scheme.{u})`, Mathlib's Scheme extends
   LocallyRingedSpace with local_affine. Correct, including empty schemes.
2. D(O_X) is the derived category of all O_X-modules: `schemeDerivedCategory X` is
   DerivedCategory of the shared `SheafOfModules (moduleRings X.toRingedSpace)`.
   The HasDerivedCategory binders choose localizations, including those of the over
   sites required by the recorded IsPerfect definition. They impose no geometric
   restriction. Universes u and w are explicitly bound. Correct.
3. K and M are quasi-coherent complexes: `(K M : schemeDerivedQCohCategory X)`;
   its full subcategory property requires every integral-degree cohomology sheaf to
   satisfy Mathlib `SheafOfModules.IsQuasicoherent`. Correct.
4. K is perfect: `hK : Scheme.IsPerfect X K.obj`, the recorded pointwise open-local
   strictly-perfect model definition (bounded terms, retracts of finite free modules).
   No stronger hypothesis. Correct.
5. Kdual is RHom(K,O_X), perfect and quasi-coherent: `Kdual : schemeDerivedQCohCategory X`,
   `hdual : Kdual.obj = ...derivedInternalHom... (op K.obj, 𝟙_ ...)`, and
   `Scheme.IsPerfect X Kdual.obj`. The original statement omitted quasi-coherence of
   the dual; repaired by using the full subcategory carrier. Equality transports the
   identity through `eqToHom hdual`; no unspecified model replaces RHom. Correct.
6. Evaluation is the adjoint of identity, not an arbitrary map: the equation for `ev`
   applies the first chosen equivalence from `scheme_derivedInternalHom_adjunction`
   to `eqToHom hdual`. The original existential ev lacked this equation. Repaired.
   The chosen equivalence is precisely the dependency's shared natural adjunction;
   no second adjunction or RHom is defined.
7. The comparison for M is the adjoint of `1_M tensor ev`: the family `comparison N`
   is pinned by the equation whose right side is the associator, `N.obj ◁ ev`, and
   the right unitor. `IsIso (comparison M)` is the requested conclusion. The same
   family includes N=K solely to express the source's coevaluation definition, with
   `IsIso (comparison K)` as required there. Its maps at other N are only defined
   by the adjunction; no extra hypothesis or unrequested isomorphism assertion is
   introduced. The original unconstrained comparison was weaker. Repaired.
8. Biduality is the adjoint of symmetry followed by ev: the equation for `bidual`
   uses the symmetry family extracted from the very same dependency theorem, and
   `IsIso bidual`. The original arbitrary bidual and arbitrary symmetry were not
   this canonical construction. Repaired.
9. Coevaluation is uniquely the preimage of identity at N=K: the equation
   `e unit K K (η ≫ comparison K) = (λ_ K.obj).hom` and the identically phrased
   implication for every z say exactly this. The original `z ≫ symm.hom ≫ ev = id`
   is a trace condition, not this condition; it need not characterize coevaluation
   (already finite free modules of rank two have many trace-one endomorphisms).
   Replaced, without changing the node.
10. Both zig-zags use the displayed ev and η: `∃ p : ExactPairing K.obj Kdual.obj,
    p.evaluation' = ev ∧ p.coevaluation' = η`. I read Mathlib ExactPairing's two
    fields: they are exactly the associator/unitor forms of both triangle identities.
    The original unrelated `Nonempty (ExactPairing ...)` did not connect its maps
    to ev and η. Repaired. Since both objects are QCoh and the QCoh category is
    full, these are exactly the same morphisms and equations in D_QCoh; no separate
    private monoidal category is introduced.
11. For every scheme morphism, canonical dual base change is invertible:
    `∀ (T : Scheme.{u}) (g : T ⟶ X) [HasDerivedCategory ...], ∃ bc ...`;
    its equation under the adjunction on T is the tensorator of the shared new
    `derivedPullbackMonoidalModel g`, followed by `(derivedPullback g).map ev`
    and the inverse unit isomorphism. `IsIso bc` is precisely the conclusion.
    The original base-change map had no defining equation. Repaired.

Dependency audit: Scheme, IsPerfect, schemeDerivedCategory, schemeDerivedQCohCategory,
derivedPullback, derivedInternalHom, CochainComplex.mapBifunctor and the sheaf curried
Tensor are the recorded notions, not replacements. I read the Mathlib Scheme and
bifunctor source signatures as well as DerivedCategory.lean, PerfectComplex.lean,
DerivedPullback.lean, DerivedInternalHom.lean, DerivedInternalHomAdjunction.lean,
DerivedPullbackTensorProduct.lean and DerivedTensorStructure.lean. The tensor-product
pullback theorem is stated on K-flat complex models rather than as a tensorator of
the global derived tensor. It is usable as written; a missing canonical monoidal model
is added below rather than replacing or weakening that dependency.

Edge cases: zero K and zero M are permitted; the identity-preimage condition remains
valid for zero K (the discarded trace condition would instead have been vacuous).
The empty scheme and morphisms from empty schemes are permitted, with IsPerfect's
pointwise condition vacuous as it should be. Finite-free local rank zero is allowed
by Fin 0. There is no finite index-set binder or nonemptiness assumption, no degree
restriction and no n=0 exclusion. No field or characteristic hypothesis occurs.
T and X share the scheme universe as the recorded derivedPullback requires; arbitrary
scheme sizes can be enlarged into this universe. w is the independent localization
morphism universe throughout. No variable or universe is auto-bound.

Independent searches, using different phrases from the worker:

- LeanFinder: `dual of perfect complex evaluation coevaluation derived pullback`:
  eight generic rigid-category/finite-dimensional vector-space results, none for
  perfect O_X-complexes.
- Loogle: `ExactPairing`, then `Functor.CoreMonoidal`: service replies unknown
  identifier and returns zero hits; this is not positive evidence of absence.
- LeanSearch: `monoidal derived pullback of sheaves of modules on a scheme`:
  service unavailable (Internal Server Error), recorded as unavailable without a
  mathematical verdict; supplemented by LeanFinder and the local searches.
- LeanFinder: `canonical monoidal tensor comparison derived inverse image O_X
  modules scheme`: eight underived module/presheaf results, none for this model.
- msearch grep: `derivedPullbackMonoidal|IsDerivedPullbackMonoidal|
  perfect_rhom_tensor_comparison`: zero hits on the base.
- Independent rg searches on Mathlib, WeilConjectures, lean/Sheaf and dag/nodes
  for `dual.*perfect`, `perfect.*dual`, `rhom.*perfect`, and
  `derived.*pullback.*monoidal` find point-module perfect duality and etale/proetale
  coefficient duality, different categories. The generic CoreMonoidal API is reused.
  SingleComplexInheritedTensorCondition asserts existence of some monoidal structure
  but has unrelated hypotheses and no canonical tensorator specification; it does
  not supply this definition. No exact existing statement/model was found.

H5/H6/H8/H9: all theorem proofs remain sorry, no proof was attempted. Definitions contain
no sorry. The new model chooses data from the named, fully specified existence theorem,
as the recorded derivedPullback does; the project currently permits this spec-pinned
pattern (STATE, DATA FROM SORRIED EXISTENCE). There is no file-local notation, private
notion or file-local instance: instances inside the model predicate's body merely
elaborate its public type. Added the copyright header, moved the module docstring
immediately after imports, removed the extraneous 0A9T citation, and expanded the proof
docstring to all four node steps, including quasi-coherence and checking invertibility
locally rather than gluing morphisms. Node lean.statement is regenerated verbatim
from the signature using the project's declaration reader.

The blueprint search `tools/blueprint_refs.py search monoidal pullback` found two
trace-formula coefficient nodes (def-trf-supported-pairing and
prop-trf-adic-coefficient-morphism-systems). Their statements concern constant
etale/proetale coefficient systems, not O_X-module derived pullback; neither defines
this model. The dry run also found that the item's stored blueprint via list was
incomplete relative to the full created.item ancestry. I corrected only the new
node's via list using blueprint_refs.chain; the item's historical fields are untouched.

Validation: both modules type-check together locally; the final deliver2 dry run
passes the maintainer's preflight and server compilation without warnings.
Only the item statement and the new model's specified existence theorem have sorry.
No dependency module was rewritten and the node's natural-language statement is unchanged.
