## Worker report

The module `lean/Sheaf/AlgebraicGeometry/SeparatedAffineCoverCriterion.lean` states
`AlgebraicGeometry.separated_of_affine_open_cover`, with proof `sorry`.
The binders render the node as follows: `S` is affine via `[IsAffine S]`, `f : V ⟶ S`
is the morphism, `A` and `Vₐ : A → V.Opens` give the indexed open cover, and
`hcover : ⋃ a, (Vₐ a : Set V) = Set.univ` expresses that it covers. `haff` says each
open is affine and `haffint` says each pairwise intersection (the infimum of opens)
is affine. For each pair, `hsurj` supplies a ring hom from the tensor product over
ℤ of the two section rings to the intersection section ring, asserts surjectivity,
and identifies pure tensors with the product of the two restriction maps. The
conclusion `IsSeparated f` is the diagonal closed-immersion condition.

Dependencies used are Mathlib's `AlgebraicGeometry.Scheme` (via the scheme types),
`AlgebraicGeometry.IsSeparated` (Mathlib.AlgebraicGeometry.Morphisms.Separated),
and the structure-sheaf section notation `Γ` and presheaf restriction maps from
Mathlib.AlgebraicGeometry.Scheme. The project's dependency records are used by
these Mathlib definitions; no private copy is introduced.

Edge cases checked: the index type `A` may be empty (the cover hypothesis then rules
out a nonempty `V`), repeated or equal opens are allowed, pairwise intersections may
be empty, and the statement imposes no finiteness or nonemptiness assumptions. The
scheme universe `u` and index universe `v` are explicit.

Searches: Lean source grep for separated affine-cover criteria and the node id found
no existing project declaration. LeanFinder/LeanSearch searches for separatedness
criteria with affine covers and tensor restriction maps found only general
`IsSeparated` declarations, not this criterion. Mathlib grep of
`AlgebraicGeometry/Morphisms/Separated.lean` found no affine-cover tensor criterion.

No statement correction or `STATEMENT-DISPUTED` applies.


## Second reading by H1

I read the node and module independently against Stacks `schemes.tex`,
`lemma-characterize-separated` (Tag 01KP), lines 4157–4211, including the
surrounding proof. The local repository has no fetched Stacks .tex files, so I
read the upstream raw .tex from
https://raw.githubusercontent.com/stacks/stacks-project/master/schemes.tex
(saved only in this item's scratchpad). The source introduces an arbitrary
morphism of schemes; there are no standing field, characteristic, Noetherian,
finiteness, or nonempty hypotheses. Part (2) gives the local criterion for any
pair of points over the same base point. The node specializes it to a fixed
cover and an affine base, so every pair of cover members maps to the same
common affine open S. This specialization is mathematically sound.

Object/hypothesis/conclusion checklist (each verdict: exact):

- Schemes S and V: `{S V : Scheme.{u}}`; `def-pc-scheme` records Mathlib
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`. I opened Scheme.lean: Scheme
  is a locally ringed space locally isomorphic to affine spectra, and Hom is
  a morphism of locally ringed spaces. These are the node's objects.
- S affine: `[IsAffine S]`. AffineScheme.lean defines this as the canonical
  morphism to Spec Γ(S) being an isomorphism, equivalent to being a spectrum.
- Morphism f: `(f : V ⟶ S)`, no property assumed of f.
- Indexed opens: `(A : Type v) (Vₐ : A → V.Opens)`. Scheme.Opens is the
  topological opens, with its canonical open subscheme; no bundled chosen
  spectra or additional algebra structure is required.
- Cover of all V: `hcover : ⋃ a, (Vₐ a : Set V) = Set.univ`.
- Each cover member affine: `haff : ∀ a, IsAffineOpen (Vₐ a)`.
  I opened IsAffineOpen: it is precisely `IsAffine` of the open subscheme.
- Every pairwise overlap affine: `haffint : ∀ a b,
  IsAffineOpen (Vₐ a ⊓ Vₐ b)`; infimum is intersection of opens.
- Canonical section-ring map over ℤ surjective for every a,b: `hsurj` has
  `∀ (a b : A), ∃ φ : TensorProduct ℤ (Γ(V, Vₐ a)) (Γ(V, Vₐ b)) →+*
  Γ(V, Vₐ a ⊓ Vₐ b), Function.Surjective φ ∧ ...`. The equation for every
  pure tensor uses `TensorProduct.tmul ℤ x y` and the product of
  `V.presheaf.map (homOfLE inf_le_left).op x` and the analogous right
  restriction of y. Γ is the scheme structure-sheaf section ring, not the
  section group of another sheaf. Existential φ is equivalent to the stated
  canonical map: the ℤ-algebra maps are the canonical integer actions, the
  two restriction maps commute, and pure tensors additively generate, so the
  pure-tensor equation uniquely determines the ring homomorphism. It adds
  no arbitrary choice or stronger hypothesis. The quantifiers have the same
  order: each pair, then its ring map, then all sections x,y.
- Conclusion: `IsSeparated f`. I opened Separated.lean: its only field is
  `IsClosedImmersion (pullback.diagonal f)`. Thus this includes exactly the
  node's explanatory diagonal clause, not a different notion of separated
  scheme. `def-weil-proper-morphism` records this Mathlib class amongst its
  declarations; properness is not assumed. `def-pc-fibre-product` records
  `CategoryTheory.Limits.pullback` and its projections, read against the
  node's universal property. `def-weil-closed-immersion` is a Mathlib leaf
  with match `AlgebraicGeometry.IsClosedImmersion` (no lean record); I opened
  ClosedImmersion.lean, whose fields are a closed embedding and surjective
  stalk maps, the sheaf-surjectivity condition of that dependency node.

Edge cases: A may be empty and has independent arbitrary universe v; there
is no Nonempty or finite-instance binder. With A empty, hcover forces V to
be empty, correctly retained. Empty opens and empty overlaps are allowed:
their section rings are zero rings, which are valid commutative rings and
ℤ-algebras. S may itself be empty, and neither V nor S must be nontrivial.
The universe u is arbitrary; schemes of differing sizes can be placed in a
common universe, and no quantification over test schemes/rings in a smaller
independent universe occurs. Characteristic is unrestricted because the
base tensor ring is ℤ, not a field. There is no integer-degree parameter n.

Independent searches on 2026-10-11:

- LeanFinder through msearch: “diagonal closed immersion from affine charts
  whose overlap restriction tensor map is onto”: eight results, including
  `isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange`. I opened
  that declaration: it only proves closed immersion on the diagonal range
  of same-chart pieces, and has no affine-overlap/surjectivity criterion;
  not an exact match. The remaining results concern immersions, affine
  properties, unramified morphisms, or already separated schemes.
- Loogle through msearch: `AlgebraicGeometry.IsSeparated,
  AlgebraicGeometry.IsAffineOpen`: zero hits.
- LeanSearch through msearch: “If affine chart overlaps are affine and
  multiplication of restricted sections gives a surjective tensor ring
  map, the scheme morphism to an affine base is separated”: service unavailable
  (Internal Server Error), recorded as unavailable, with no negative verdict.
- Independent rg of Mathlib Separated.lean and the source project's
  WeilConjectures/AlgebraicGeometry and repository lean/Sheaf/AlgebraicGeometry
  using separated/cover/intersection and surjective/tensor combinations:
  no exact criterion. Project results include AmpleSeparated and
  EtaleAffineCoverStratification, which cite this node rather than state it.
  The theorem's full name and separated-affine-cover combinations have no
  match in dag/lean_names_upstream.json or the source/Mathlib declarations.

Mismatch found and repaired: H8, the original declaration docstring only
summarized the proof in one sentence. It now gives all five node steps,
including the covering argument, affine tensor-ring identification, diagonal
pullback and restriction-map identification, factorization of the ℤ map,
and the closed-immersion criterion, with their dependency ids. H9, the
project example's copyright/license/author header was missing; added it and
placed the module docstring directly after imports. No theorem signature,
node statement, dependency, or Lean record changed. There are no new nodes,
no dependency modules, no hollow definitions, and the sole proof remains
`sorry`; no mathematics was proved in stage 2. Every variable and universe
is explicitly bound, and the node's lean.statement is verbatim the signature.

Validation: the original statement compiled cleanly with scompile; the
repaired module is recompiled before delivery, and deliver2 preflight is run.
