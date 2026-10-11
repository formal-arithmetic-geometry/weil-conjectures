## Worker report

The main module `Sheaf.AlgebraicGeometry.AffinePerfectMapLift` states
`AlgebraicGeometry.Scheme.exists_perfect_map_lift_of_isAffine`, with `sorry` only.
The auxiliary module defines the missing derived tensor augmentation relation in full;
its data contains no sorry. No original statement correction is needed.

Hypotheses and clauses, individually:
- Scheme X: `(X : Scheme.{uX})`; affine: `[IsAffine X]`.
- Quasi-compact open U: `(U : X.Opens) (hU : IsCompact (U : Set X))`.
- E' in D_QCoh(O_X): `(E' : schemeDerivedQCohCategory X)`. The `.obj` is its underlying
  object in exactly the shared D(O_X), with quasi-coherent cohomology in every degree.
- A in D(O_X), perfect: `(A : schemeDerivedCategory X) (hA : IsPerfect X A)`.
- Every alpha on U: the binder `α` is a morphism between the derived restrictions of
  A and E'.obj using `SheafOfModules.overFunctor.mapDerivedCategory` on the open site.
- A' exists and is perfect: `∃ (A' I : schemeDerivedCategory X) ... IsPerfect X A'`.
- Beta and gamma exist: `β : A' ⟶ A` and `γ : A' ⟶ E'.obj`.
- Beta is an isomorphism on U: the witness `bU` is an isomorphism with
  `bU.hom = ...map β`; this identifies its inverse with beta's inverse.
- Alpha equals gamma restricted composed with beta's inverse:
  `α = bU.inv ≫ ...map γ` (Lean composition applies the leftmost map first).
- A' = A tensor-derived I, I perfect, beta induced by I to O_X:
  `IsPerfect X I ∧ IsDerivedTensorAugmentation X A I A' β`. The relation uses actual
  K-flat representatives, total tensor, the tensor map of an augmentation and its
  canonical right unitor; it is not an unconstrained tensor functor or arbitrary map.
- Preservation of support on every closed T: `∀ T : Set X, IsClosed T → ...` says that
  if A is zero on all opens disjoint from T, the SAME A' is zero on all such opens.
  This is exactly support containment: the complement of a closed T is itself an open,
  and conversely restrictions of a zero object are zero. No closed set is fixed in advance.
- The `HasDerivedCategory` binders on X and all its opens only supply the shared
  localization carriers required by the recorded definition of perfectness. Both universe
  variables are explicit; no boundedness, Noetherian, characteristic or support hypothesis
  has been added.

Dependency declarations read and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `Scheme.IsPerfect`; its definition uses the
  localized-site derived restriction and Mathlib's standard sheaf-module Abelian instance.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat` and the tensor zero-preservation
  instances. The existing generic notion is reused for X.sheaf.
- `Mathlib.Algebra.Homology.BifunctorShift`/`Bifunctor`: `CochainComplex.mapBifunctor`,
  `HomologicalComplex.mapBifunctorMap`; the signed total tensor and its induced map.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`: `SheafOfModules.tensorClosed`.
  Only its proof of `MonoidalPreadditive` is selected to make the canonical complex unitor
  available. The Abelian or derived-category structure is never chosen again.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal` (through KFlat):
  `SheafOfModules.monoidalCategory`, the established sheaf tensor, with unit O_X.
- `Mathlib.Algebra.Homology.Monoidal`: `HomologicalComplex.tensorUnit`, `rightUnitor`.

Edge cases checked against the mathematical statement: empty scheme and U = empty are
allowed; U = X is allowed (I = O_X, beta identity works); A = zero and E' = zero are allowed;
E' may have unbounded cohomology in either direction. Empty T expresses A = zero, while
T = X makes support containment vacuous as it should. The source's D_QCoh condition on A
is automatic from perfectness, so its omission in the node is not a mathematical defect.
No independent universe for test objects occurs. The derived tensor relation does not
restrict representatives to finite/free complexes, preserving the full statement.

Searches for the item:
- msearch.py leanfinder, `lift morphism from perfect complex on quasi-compact open of an
  affine scheme`: 8 unrelated affine limits, ring sections, gluing and scheme lifts;
  no derived perfect-map lifting statement.
- msearch.py loogle, `CochainComplex.IsKFlat, HomologicalComplex.mapBifunctorMap`:
  `OK 0 hit(s) | loogle: unknown identifier 'CochainComplex.IsKFlat'` (project declarations
  are not indexed there).
- msearch.py grep, `perfect.*lift|lift.*perfect`: 18 perfect-ring/closure hits, no match.
- rg in WeilConjectures, `lem-sc-affine-perfect-map-lift|perfect.*lift|lift.*perfect`:
  only a Lie algebra comment and abstract-category triangle comment, no match.
- rg in lean/Sheaf for perfect, derived restriction and tensor: existing definitions and
  related lifts, no statement for this item. rg in dag/lean_names_upstream.json for
  the proposed declaration names: no collision.
- LeanSearch for the augmentation notion: unavailable (Internal Server Error); retained
  as unavailable in the new node. LeanFinder and literal grep completed independently.

Source read: `lemma-lift-map` in `/home/ubuntu/c1-stacks-review/perfect.tex`, lines
3354-3395, the local copy of Stacks Tag 08EH. The repository literature file is absent
on this machine. Its proof supplies the Koszul augmentation, tensor construction, and
beta exactly as recorded by the node. The node's support consequence follows by restriction.

Server check: both delivery modules compile together without errors or warnings (5.6 s).
No proof beyond the single expected theorem sorry was written.

## New nodes

`def-sc-derived-tensor-augmentation` defines precisely the combined object/map description
B = A tensor-derived I and beta = id_A tensor-derived u, after the canonical unitor.
Its source is Tag 08EH's augmentation construction, with the K-flat convention from
Tags 06YS/06YU. It reuses `def-pc-kflat-complex`, `def-pc-tensor-complex-sheaves`,
`def-pur-sheaf-tensor-product` and `lem-pc-sheaf-modules-tensor-closed`. The formula is
transported by isomorphisms from K-flat models; `u : J ⟶ O_X[0]` represents
I to O_X using the inverse of the model isomorphism. A derived map admits such a roof:
represent it by a roof ending in O_X[0] and replace its source by a K-flat complex.
Thus these witnesses describe the existing derived operation, with no extra geometric
hypothesis and no global strictly perfect representative requirement.

The new node records the searches with their results: LeanSearch unavailable;
LeanFinder returned 8 flat-module/tensor and scheme-flatness statements; literal rg
`IsDerivedTensorAugmentation|derived tensor augmentation|tensor augmentation` gave
zero hits in Mathlib, WeilConjectures, lean/Sheaf and dag/nodes. `blueprint_refs.py search
'derived tensor'` found 35 nodes, none giving this scheme-level augmentation predicate.
The existing pro-etale and etale derived tensors have different sites and coefficients;
the scheme tensor-cohomology vanishing predicate does not encode an induced map.

## Second reading by H1

Independent reading of the sandbox's two node files and two Lean modules, against
Stacks `perfect.tex`, `lemma-lift-map` (Tag 08EH), lines 3354–3395 in
`/home/ubuntu/c1-stacks-review/perfect.tex`. The source introduces an arbitrary affine
scheme and a quasi-compact open; there is no ambient field, characteristic,
Noetherian or boundedness assumption. Its E is in D_QCoh and perfect; the node instead
says A is perfect in D(O_X), which implies the source's quasi-coherence condition.
The source's proof, not just its displayed conclusion, specifies the augmentation
inducing beta. Support containment is the immediate tensor consequence spelled out
in the node's fourth proof step. No statement correction is needed.

The complete object/hypothesis/conclusion inventory and its Lean rendering:

- X is a scheme and affine: `(X : Scheme.{uX}) [IsAffine X]`. Read Mathlib's
  `Scheme` structure (locally affine locally ringed space) and `IsAffine` (the canonical
  map to Spec of global sections is invertible). Verdict: exact, no extra geometry.
- U is an open of X and quasi-compact: `(U : X.Opens)` and
  `(hU : IsCompact (U : Set X))`. Compactness here does not assume Hausdorffness and
  means the node's quasi-compactness. Verdict: exact.
- E' is in D_QCoh(O_X): `(E' : schemeDerivedQCohCategory X)`. I opened
  `DerivedCategory.lean`: its full-subcategory property requires the homology sheaf
  to be quasi-coherent for every integer. `E'.obj` is its underlying object in the
  SAME D(O_X). Verdict: exact and unbounded, not D-plus or bounded D.
- A is an object of D(O_X) and perfect: `(A : schemeDerivedCategory X)` and
  `(hA : IsPerfect X A)`. I opened `PerfectComplex.lean`: every point has an open
  neighbourhood where derived restriction is isomorphic to a bounded complex whose
  terms are retracts of finite free sheaves. Verdict: the recorded notion, not a
  global strictly perfect model or a bounded complex of arbitrary coherent sheaves.
- Alpha is any derived morphism A restricted to U to E' restricted to U: the `α`
  binder uses `SheafOfModules.overFunctor ... U` followed by `mapDerivedCategory` on
  both objects. Verdict: the project's shared localized-open restriction, with no
  extension of alpha assumed.
- A' exists on X and is perfect: existential `A' : schemeDerivedCategory X` and
  `IsPerfect X A'`. Verdict: exact.
- Beta maps A' to A, gamma maps A' to E': `(β : A' ⟶ A)` and
  `(γ : A' ⟶ E'.obj)`. Verdict: correct objects and directions.
- Beta is invertible on U: existential `bU` between the restricted objects, with
  `bU.hom = ...map β`. Verdict: precisely invertibility of the given beta, not an
  unrelated isomorphism of the objects.
- The factorization is alpha = gamma on U composed with beta on U inverse:
  `α = bU.inv ≫ ...map γ`. Lean's composition is left-to-right. Verdict: exact order.
- The same A' is A tensor-derived I, for a perfect I, and beta is induced by a map
  I to O_X: existential `I`, `IsPerfect X I`, and
  `IsDerivedTensorAugmentation X A I A' β`. I expanded this definition below.
  Verdict: both the object and the induced morphism are specified.
- Closed support is preserved: `∀ T : Set X, IsClosed T → ...` takes vanishing of A
  on every open disjoint from T and concludes vanishing of that SAME A' there.
  Taking the open complement of T shows equivalence with support containment;
  conversely restrictions of a zero object are zero. Verdict: exact, and the
  witnesses A', I, beta, gamma precede T, so support is preserved simultaneously.
- Infrastructure: the two `HasDerivedCategory.{wD}` binders supply the localization
  carriers on X and its opens required by `IsPerfect`; Mathlib's standard Abelian
  instance is used throughout. Verdict: no alternate Abelian structure, no new
  finiteness/geometric assumption, and no small-universe test-object quantifier.

New definition `def-sc-derived-tensor-augmentation` was independently read as a
stage-1 definition and matched to its module. I also read `sites-cohomology.tex`,
`lemma-K-flat-resolution` (06YS), lines 3207 onward, and the construction preceding
`definition-derived-tor` (06YU), and checked the tag-to-label map. These work on any
ringed site. In Lean, existential P and J are complexes of the actual O_X-module
category; both satisfy the shared `CochainComplex.IsKFlat` predicate. `eA` and `_eI`
identify Q(P), Q(J) with A, I. `eB` identifies the total tensor Q(P tensor J) with B.
The chain map `u` ends in `HomologicalComplex.tensorUnit`, which I checked in
Mathlib is the single complex in degree zero of the sheaf monoidal unit O_X.
`mapBifunctorMap (𝟙 P) u` is the actual induced tensor map, and
`HomologicalComplex.rightUnitor P` is the canonical total-complex right unitor.
The equation begins with `eB.inv` and ends with `eA.hom`, matching the node's formula
exactly. The represented derived augmentation is `_eI.inv ≫ Q.map u`; a roof for
any derived morphism into O_X can be replaced at its source by a K-flat resolution,
so requiring a chain representative here adds no mathematical restriction.

I opened the dependency nodes and declarations for `def-pc-kflat-complex`,
`def-pc-tensor-complex-sheaves`, `def-pur-sheaf-tensor-product`, and
`lem-pc-sheaf-modules-tensor-closed`, as well as the scheme, derived-category and
perfectness dependencies above. KFlat uses acyclicity of total tensor with every
acyclic complex. Mathlib `CochainComplex.mapBifunctor` and its map are the signed
bicomplex totalization. The upstream sheaf monoidal structure is sheafification
of sectionwise tensor and has O_X as unit; `tensorClosed` supplies only the
MonoidalPreadditive proof selected here, not a second Abelian instance or a chosen
localization. The Prop definition contains concrete existential model data and
no sorry. No private replacement of any dependency or missing dependency module
was found.

Edge cases: U empty has no nonempty-cover assumption and its restriction category
is zero; the lift can be obtained by the zero factor. U = X allows the unit factor
and beta identity. The empty scheme is allowed (perfectness is pointwise and thus
vacuous there, appropriately). A = zero and E' = zero are allowed. T empty means
A itself vanishes and forces the same for A'; T = X imposes no support restriction.
There is no integer n or characteristic binder to exclude n = 0 or any
characteristic. Complexes have all integer degrees and no boundedness condition
on E'. Scheme universe uX and localization morphism universe wD are explicit;
there is no separate smaller universe of test rings or schemes.

Independent searches, with words differing from the first worker's:

- msearch LeanFinder: `extend derived morphism from open subscheme by perfect Koszul
  tensor factor` returned eight formally-unramified, immersion, ideal-sheaf and
  germ-lifting declarations; none is this theorem.
- msearch Loogle: `"tensor", "DerivedCategory"` returned zero hits.
- msearch LeanFinder: `derived tensor morphism from product to factor via unit
  augmentation` returned eight Cartesian/Dialectica tensor-projection and unitor
  declarations; none is this sheaf derived-augmentation relation.
- msearch grep: `DerivedTensor|tensor.*[Aa]ugment|[Aa]ugment.*tensor` returned five
  augmented-simplex-category hits, no matching notion.
- Local rg of Mathlib, WeilConjectures, lean/Sheaf and dag/nodes for Koszul lifts,
  perfect extensions, and tensor augmentations found the relevant Koszul DAG
  lemmas, upstream projective-space Koszul maps, and unrelated Amitsur
  augmentations; none provides the theorem or the scheme-derived relation.
  `blueprint_refs.py search 'tensor augmentation'` found zero blueprint nodes.
  Searching both proposed declaration names in upstream names, Mathlib,
  WeilConjectures and lean/Sheaf found no collision.
- I additionally opened the nearby `schemeDerivedTensorCohomologyVanishes`
  definition: it tests vanishing after tensor with a degree-zero sheaf and cannot
  encode an induced augmentation map. DerivedPullbackTensorQCoh likewise describes
  tensor models without the map to A. Neither is the new notion. The worker's
  recorded LeanSearch service failure is retained as unavailable, not a negative
  mathematical search result.

Mismatch review: no mathematical or Lean mismatch was found. The item's stored
blueprint via is a short chain; preflight resolves the full chain to the blueprint
ancestor, as the worker's new definition already did correctly. My initial
metadata adjustment to the short chain was rejected by dry-run preflight. I
restored the original full chain required by preflight, so no net node or module
repair remains. The new node otherwise has the required chapter/unit,
definition/split status, empty proof and proof_deps, null mathlib_match, created
record, none audits, searched notion and matching Lean record. There is no
statement_change or citer correction.

The main docstring reproduces all four proof steps, including the named RHom,
open-representability, perfect-tensor and tensor-Hom dependencies. Both modules
have source and blueprint docstrings, topic paths and headers, and every line
fits 100 characters. The only new theorem proof is sorry. All variables and
universes are explicitly bound. The project's signature reader confirms both
node lean.statement fields equal their file signatures modulo whitespace.
Both modules compiled together with scompile.py on the server in 5.7 seconds,
with no errors or warnings.
