## Worker report

The module `Sheaf.AlgebraicGeometry.GeneralizingSubsetAffineEnvelope` states
`AlgebraicGeometry.GeneralizingSubset.affine_envelope`, with its proof postponed.
The node's mathematical statement, dependencies, and proof are unchanged.

The eight preceding definitions name the actual objects and maps in this theorem:
`sections`, `envelope`, `map`, `space`, `unit`, `image`, `boundary`, and `localSubset`.
They contain real data, without postponed proofs or choices of unspecified objects.
They are helpers of this node's canonical-envelope construction, not independent
replacement notions. In particular, `space` bundles the recorded ringed subspace
with locality proof data; it does not construct a second inverse-image sheaf.

Hypothesis and clause correspondence:

- A commutative ring A and S = Spec A: `(A : CommRingCat.{u})`, with `Spec A`
  throughout. The universe u is arbitrary and explicitly bound.
- H is an arbitrary subset: `(H : Set (Spec A))`.
- Stability under generalization: `hgen` says that `s ∈ H` and `t ⤳ s`
  imply `t ∈ H`. The direction of specialization is intentional: t is the
  generalization and s is its specialization, or s lies in closure {t}.
- Retrocompactness: `hretro : IsRetrocompact H`. Mathlib's definition is exactly
  compactness of H intersect U for every compact open U.
- The induced ringed space E: `space A H hl` is exactly
  `LocallyRingedSpace.locallyRingedSubspace (Spec A).toLocallyRingedSpace H hl`.
  Its ringed-space component is the dependency's `ringedSubspace`, whose sheaf
  is the inverse-image sheaf under the subtype inclusion.
- Locality is a conclusion: `∃ hl : ∀ x : H, IsLocalRing (...)`.
  It is not an additional hypothesis on H.
- C = Γ(H, O_S restricted to H): `sections A H` evaluates that actual
  `ringedSubspace` presheaf at `op ⊤`.
- V = Spec C: `envelope A H` is `Spec (sections A H)`.
- h is induced by A → C: `map A H` is `Spec.map` of `toSpecΓ A`
  followed by the top component of the specified ringed-subspace inclusion.
  The `toSpecΓ A` factor is the canonical A → Γ(Spec A) identification;
  thus this is restriction from A, with no arbitrary structural map.
- Canonical k: `unit A H hl` is Mathlib's `LocallyRingedSpace.toΓSpec`
  for this actual E. The first conjunct also records
  `toSpecΓ (sections A H) ≫ (unit A H hl).c.app (op ⊤) = 𝟙 _`,
  the precise normalization corresponding to the identity on C.
- Identification with the induced ringed image: the first existential
  isomorphism has target `ringedSubspace V (image A H hl)` and satisfies
  `e.hom ≫ ringedSubspaceι V (image A H hl) = k.toShHom`.
  This records the actual sheaf map of k, not just a homeomorphism of points.
- h composed with k is the inclusion: the next conjunct is the equality
  `k.toShHom ≫ h.toLRSHom.toShHom = ringedSubspaceι S H`.
- h inverse H = k(H): `map A H ⁻¹' H = image A H hl`, where `image`
  is the range of the specified k's base map.
- B = h(V minus k(H)): `boundary A H hl` is `map A H '' (image A H hl)ᶜ`.
- E is a scheme exactly when closure B misses H: the biconditional uses
  `∃ X : Scheme.{u}, Nonempty (X.toLocallyRingedSpace ≅ space A H hl)`
  and `closure (boundary A H hl) ∩ H = ∅`. Existence of this presentation
  is invariant under isomorphism and exactly means that this locally ringed
  space is a scheme, including its given sheaf.
- Its canonical morphism, whenever E is a scheme: for every scheme X and
  locally ringed isomorphism `e : X.toLocallyRingedSpace ≅ space A H hl`,
  the theorem supplies `f : X ⟶ Spec A` with its ringed map equal to
  `e.hom.toShHom ≫ ringedSubspaceι S H` and `QuasiCompact f ∧ Flat f ∧ Mono f`.
  This is a statement about the canonical inclusion, not about the existence
  of some morphism with these three properties.
- k surjective iff k is an isomorphism: the first displayed biconditional
  uses `Function.Surjective k.base ↔ IsIso k` in locally ringed spaces.
- k is an isomorphism iff E is affine: the next biconditional asserts a
  scheme presentation X with `IsAffine X` and a locally ringed isomorphism
  to the given E. Thus the three-way equivalence is two adjacent iff clauses.
- Every point s, with no restriction s ∈ H: the last universal quantifier
  is `∀ s : Spec A`.
- S_s and its canonical map: the ring is `(Spec A).presheaf.stalk s` and
  the map is exactly `(Spec A).fromSpecStalk s` from the recorded dependency.
- H_s: `localSubset A H s` is its inverse image of H.
- The two hypotheses hold again: the first two local conjuncts state
  generalization stability and `IsRetrocompact (localSubset A H s)`.
- Its induced ringed space is locally ringed: `∃ hls` supplies precisely
  the local-ring proofs for the same inverse-image-sheaf construction.
- Its canonical affine envelope V_s: the same `envelope` definition is
  evaluated on the actual stalk ring and H_s. Its canonical unit and map
  are the same `unit` and `map` definitions on those inputs, so the theorem
  above also applies to this pair using the asserted hypotheses.
- Canonical localization comparison: q maps E_s to E, has base
  `(q.base x).val = c_s x.val`, and its sheaf map commutes with the two
  specified ringed-subspace inclusions and `c_s.toLRSHom.toShHom`.
  The inclusion and the inverse-image adjunction determine this map;
  it is not an arbitrary map on sections.
- Canonical S_s-isomorphism: the existential `e : V_s ≅ pullback h c_s`
  is characterized by BOTH projection identities. Its first projection is
  `Spec.map (LocallyRingedSpace.Γ.map q.op)`, the spectrum of pullback of
  sections by this canonical q. Its second projection is exactly h_s.
  These identities fix the comparison and its structure over S_s.
- Image after this identification: `image` for the local pair equals
  `(e.hom ≫ pullback.fst h c_s) ⁻¹' image A H hl`.
- Boundary image after localization: the final conjunct is equality of
  the local `boundary` with `c_s ⁻¹' boundary A H hl`. Both directions
  of the asserted equality are retained.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Spec`, and `Spec.map`.
- `Sheaf.AlgebraicGeometry.RingedSubspace`:
  `LocallyRingedSpace.ringedSubspace`, `ringedSubspaceι`,
  and `locallyRingedSubspace`; their complete source and docstrings were read.
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`:
  `LocallyRingedSpace`, `LocallyRingedSpace.Hom`, and `Hom.toShHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`;
  its stalkwise interpretation is `Flat.iff_flat_stalkMap`.
- `def-weil-pbc-scheme-conventions` is explicitly a convention record,
  not a declaration. Its quasi-compact and affine meanings are Mathlib's
  `QuasiCompact` and `IsAffine`; monomorphism is `CategoryTheory.Mono`.
- `WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`:
  the full signatures and docstrings of `Scheme.fromSpecStalk_affine_description`,
  `fromSpecStalk_local_properties`, `fromSpecStalk_module_stalk`, and
  `fromSpecStalk_quotient_factorization` were read. The statement uses their
  actual canonical map `Scheme.fromSpecStalk`, rather than a replacement.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, and `pullback.snd`.
- The Mathlib affine adjunction and unit are used through
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`.
- The currently recorded project proof dependencies are imported without
  `public`: `WeilConjectures.Topology.SpectralGeneralizations`,
  `Sheaf.AlgebraicGeometry.IntersectionCanonicalAffineEmbedding`,
  `Sheaf.AlgebraicGeometry.QcOpenIntersectionSpectralPresentation`,
  `Sheaf.Topology.SpectralDirectedLimit`,
  `Sheaf.AlgebraicGeometry.IntersectionSectionsFlatBaseChange`, and
  `WeilConjectures.Topology.InverseImageStalk`.
  The qc-flat-monomorphism affine-neighborhood proof input has no recorded
  module yet, so there is no module to import for it in this delivery.

Edge cases checked before and after writing:

- H empty is permitted. The actual inverse-image sheaf on the empty space
  has zero global-section ring, so its envelope and image are empty. The
  boundary criterion and all three affine equivalences include this case.
- A the zero ring is permitted; there is no `Nontrivial A` assumption and
  no nonempty-point or nonempty-subset assumption. The local clause then
  quantifies over the empty set of points.
- H the whole spectrum gives the ordinary global-section spectrum and
  empty boundary. Localizing at any point recovers its full local spectrum.
- s outside H is included. The local assertions do not assume s ∈ H and
  do not throw away localizations with H_s empty.
- Generalization uses `t ⤳ s`, not the reverse specialization direction.
- Arbitrary commutative rings are allowed, with no Noetherian, finite-type,
  finite-presentation, or additional separatedness assumption.
- All constructions remain in the arbitrary universe u of A; there is no
  unrelated smaller testing universe or forced equality of universes.

Searches performed using the prescribed `msearch.py` wrapper:

- LeanFinder, query: "A retrocompact subset stable under generalization of an
  affine scheme has a canonical affine envelope and is a scheme exactly when
  the closure of the boundary image avoids the subset". Eight hits, including
  `Scheme.IsQuasiAffine`, `IsAffineOpen`, and `isRetrocompact_basicOpen`;
  none states the ringed-subspace boundary criterion or localization assertion.
- Loogle, query: `LocallyRingedSpace.toΓSpec, IsEmbedding, IsAffine`.
  Zero hits; service reported unknown identifier `LocallyRingedSpace.toΓSpec`.
  Direct source inspection nevertheless found the fully qualified unit in
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`, and the module uses it.
- Mathlib grep, query: `toΓSpec|IsRetrocompact|IsStableUnderGeneralization`
  under `AlgebraicGeometry`. Twelve hits, including the canonical unit's
  definitions and uses of retrocompact basic opens; no complete theorem match.
- LeanSearch, query: "A locally ringed subspace of an affine scheme stable
  under generalization is a scheme if the boundary of its affinization misses
  it". Eight hits concerning `Scheme.mk`, `IsOpenImmersion.scheme`,
  `IsAffine`, and `AffineScheme`; none gives the criterion.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for affine-envelope,
  generalizing-envelope, boundary-criterion, and ringed-subspace terminology.
  Found and reused `RingedSubspace`, the intersection canonical embedding,
  and Mathlib's adjunction unit. `CanonicalAffineEnvelopeDescentDatum` works
  with an already schematic quasi-affine source and cannot replace this
  theorem about a ringed subspace that need not be a scheme.
- The prescribed node-id grep in `lean/WeilConjectures` found no declaration.
  Direct `rg` of Mathlib, WeilConjectures, Sheaf, and `dag/lean_names_upstream.json`
  for `GeneralizingSubset` found no collision with the new namespace or names.

Source checked: the primary Numdam scan
https://www.numdam.org/article/SAC_1967-1968__2__A5_0.pdf, saved only under
this sandbox's `sources/`, with text inspected at printed pp.4--8 and p.13.
Proposition 2.3(iii) explicitly describes the local comparison and its
cartesian square; Proposition 2.4 gives the boundary and affine criteria.
No statement dispute, dependency repair, or statement correction is needed.

Validation: the prescribed `scompile.py Q69
lem-sfb-generalizing-subset-affine-envelope <module>` accepted both the
sandbox compilation and compilation at the final library module name,
with no errors or unexpected warnings. No global or direct Lean build ran.

## Second reading by Q69

This is the worker's second pass; the dispatcher assigns independent review
to the maintainer. Reopened the node and read the complete resulting module
against the source and the clause correspondence above. Checked especially
that generalization has the correct direction, that locality is a conclusion,
that the ringed-image isomorphism commutes with the actual sheaf map, and that
quasi-compactness/flatness/monicity belong to the specified inclusion for every
scheme presentation. Checked both affine iff clauses and the local statement
at every s, including s outside H. The local comparison has both projection
identities, so it retains the canonical pullback of sections; the final two
set equalities retain both the image and boundary-complement assertions.
No mathematical mismatch was found and no clause was removed or restricted.
