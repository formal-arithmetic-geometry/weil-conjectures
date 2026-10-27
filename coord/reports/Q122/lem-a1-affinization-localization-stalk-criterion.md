## Worker report

The module `Sheaf.AlgebraicGeometry.AffinizationLocalizationStalkCriterion` states
`AlgebraicGeometry.LocallyRingedSpace.affinization_localization_stalk_criterion`, with
one postponed proof, exactly for lem-a1-affinization-localization-stalk-criterion.
No definition, new node, dependency repair, or statement correction is needed.

Hypothesis and clause correspondence:

- The arbitrary locally ringed space is `Z : LocallyRingedSpace.{u}`. Its ring C is
  `Γ.obj (op Z)`, definitionally the sections on the top open. The canonical j is
  `Z.toΓSpec`, the unit of the recorded affine adjunction. The target
  `Spec.locallyRingedSpaceObj (Γ.obj (op Z))` is definitionally the underlying
  locally ringed space of `Spec (Γ.obj (op Z))`.
- The small nonempty directed partially ordered set is `{I : Type u}` with
  `[PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]`. Its thin category and
  `A : I ⥤ CommRingCat.{u}` encode every transition and its compatibility.
  There is no restriction on injectivity of the transition maps.
- The compatible maps r_i are `r : A ⟶ (Functor.const I).obj (Γ.obj (op Z))`.
  `_hcolim : IsColimit (Cocone.mk (Γ.obj (op Z)) r)` says that precisely these
  maps exhibit C as the colimit, rather than equating C to an unrelated chosen object.
- The prime q_z is `Z.toΓSpecFun z`. Its contraction p_i,z is the prime spectrum
  point `(Z.toΓSpecFun z).comap (r.app i).hom`, and `.asIdeal` supplies its ideal
  and primality instance to `Localization.AtPrime`.
- `_hstage` quantifies over EVERY z and i. Its existential θ is a map from that
  stage prime localization to `Z.presheaf.stalk z`. The equation
  `CommRingCat.ofHom (algebraMap ... ...) ≫ θ = r.app i ≫ Z.presheaf.Γgerm z`
  identifies θ as the germ-induced extension; the localization universal property
  makes it unique. Thus this is not an arbitrary isomorphism between the two rings.
  `IsIso θ` is precisely the assumed isomorphism of that induced homomorphism.
  Existence is a logically equivalent way to state the canonical induced map's
  property, without introducing helper definitions or proof-dependent choices.
- The first conclusion quantifies over every z. `IsIso (Z.toΓSpec.stalkMap z)`
  is the assertion about the ACTUAL stalk morphism j_z sharp. Its second conjunct
  asserts that the composite with the canonical `StructureSheaf.stalkIso` map
  from C_q is an isomorphism. The current Mathlib `stalkIso` is an algebra
  equivalence FROM the localization TO the stalk; `.toRingHom` is its correct
  direction. Consequently this composite is exactly the equivalent germ-induced
  map C_q → O_Z,z, not a separately chosen isomorphism. These conjuncts encode
  the two equivalent formulations explicitly.
- The second conclusion quantifies over every subset F and every homeomorphism
  `h : Z ≃ₜ F`, with `(∀ z, (h z).val = Z.toΓSpec.base z)` identifying its
  composite with the inclusion as the base of j. This is exactly the conditional
  homeomorphism hypothesis, and is not a global assumption on Z.
- The existential `hlocal` supplies ONLY proof that the stalks of the recorded
  `ringedSubspace` are local. `locallyRingedSubspace ... F hlocal` retains the
  exact inverse-image sheaf and the subspace topology from the dependency.
- `e : Z ≅ locallyRingedSubspace ...` is the required locally ringed-space
  isomorphism, and `ι` is a locally ringed-space morphism to Spec C. The equation
  `ι.toShHom = ringedSubspaceι ... F` fixes its underlying ringed-space map to
  the canonical inclusion and its adjunction-unit sheaf map.
  Finally `e.hom ≫ ι = Z.toΓSpec` fixes BOTH the base and the sheaf-map
  factorization to the original j. In particular no alternative structure sheaf
  on F or independent ring-sheaf isomorphism is permitted. The inclusion is
  injective, so this equality also forces the base of e to be the supplied h.

Dependency declarations used:

- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`:
  `AlgebraicGeometry.LocallyRingedSpace`, `.Hom`, `.Hom.stalkMap`, `.Hom.toShHom`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, whose underlying
  locally ringed space is `Spec.locallyRingedSpaceObj`.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`:
  `AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction`, its unit `.toΓSpec`,
  `.toΓSpecFun`, and `.Γ_Spec_left_triangle` (the latter identifies global sections).
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `Cocone.mk`, `IsColimit`;
  these are the recorded colimit dependency's universal property, not a replacement.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Sheaf.AlgebraicGeometry.RingedSubspace`: `subspaceInclusion`, `ringedSubspace`,
  `ringedSubspaceι`, `locallyRingedSubspace`, all as recorded on def-a1-ringed-subspace.
- `Mathlib.AlgebraicGeometry.StructureSheaf`: `StructureSheaf.stalkIso`, the
  localization identification supplied by the spectrum-stalk dependency.
- Proof imports retain the recorded
  `WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`
  (`AlgebraicGeometry.filteredColimitLocalizationAtPrime`) and
  `WeilConjectures.Topology.InverseImageStalk`
  (`TopCat.Sheaf.exists_inverseImage_stalk_iso_commRing`).
  `Mathlib.Topology.Sheaves.Stalks` supplies the stalk criterion, and
  `Mathlib.Algebra.Category.Ring.FilteredColimits` supplies the filtered-ring
  elementwise-colimit interface. The inverse-image adjunction is exposed by
  the public ringed-subspace dependency.

Source check: read Stacks `more-groupoids.tex`, `lemma-sits-in-functions`
(Tag 0API), including the full proof and the sentence beginning “For any e”.
The node isolates that local-ring and restricted-sheaf argument; the additional
quasi-affine hypotheses in its parent are not hypotheses of this abstract criterion.
The declaration docstring reproduces all six proof steps and names their inputs.

Edge cases: empty Z has no stalk conditions and the conditional conclusion only
allows F empty. A one-object or constant system is allowed. No stage or transition
map is required injective, and nothing requires F to be open or closed. Identity
homeomorphisms and F the whole spectrum are included. The index and ring universes
are the common u convention for these colimits, rather than an unrelated smaller
universe. Arbitrarily large individual small examples are obtained by varying u.
No nontriviality assumption is placed on stage rings; actual primes come from z.

Searches performed through msearch.py with group Q122 and this item:

- LeanFinder: “The affinization map from a locally ringed space has isomorphic
  stalks if global sections are a directed colimit of rings whose prime
  localizations map isomorphically to the stalks”. Eight hits: scheme stalk
  formulas and `Spec_map_localization_isIso`; no combined criterion.
- Loogle: `"IsLocalization", "IsColimit"`. Zero hits.
- LeanSearch: “Affinization stalk isomorphism from directed stage prime
  localizations and ringed subspace factorization”. Eight hits, including
  `StructureSheaf.stalkIso` and its localization/stalk formulas; no criterion.
- Mathlib grep through msearch.py: `isIso.*stalk|stalk.*isIso|toΓSpec` in
  AlgebraicGeometry. Hits concern open immersions, spectrum stalks, and the
  affine adjunction, with no directed-stage criterion for arbitrary LRS.
- Direct rg of `affinization|localization.*stalk|toΓSpec` and the more precise
  `affinization.*[Ss]talk|[Ss]talk.*affinization` in both `lean/WeilConjectures`
  and `lean/Sheaf`. Existing affinization material includes dual-numbers and
  derived-global-sections special cases, not this statement. Direct search for
  the item id in `lean/WeilConjectures` had no match.
- Read the full recorded ringed-subspace module and the affine-adjunction,
  localization, locally-ringed morphism, cocone/IsColimit and stalk signatures.
  The original example CompactObject Sheaf module is withdrawn; its node points
  to the upstream module, which was read instead.

Validation: scompile.py compiled both sandbox and final module successfully on
2026-10-23. The initial probe found that current `StructureSheaf.stalkIso` is an
algebra equivalence rather than a categorical iso; the signature was corrected
by using its `.toRingHom`. No error or non-sorry warning remains.
No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q122

A second in-thread reading compared the node and final file clause by clause;
no separate agent was started, as this dispatch explicitly forbids that. The
maintainer supplies the independent review of this delivery.

This reading checked the existential stage θ equation rather than merely
`Nonempty (localization ≅ stalk)`: the equation fixes the canonical map, and its
uniqueness follows from localization. It checked that the colimit cocone has C
as its vertex and r as its legs. It checked the direction and type of the
spectrum-stalk algebra equivalence against the actual current source. It also
checked that the final factorization is equality of LRS morphisms and fixes the
inclusion's sheaf map to the dependency's adjunction unit. The topology/sheaf on
F is the dependency's real construction, while hlocal changes only proof data.
All hypotheses and conclusions listed above are present; no statement correction
or further signature change was necessary after the successful compile.
