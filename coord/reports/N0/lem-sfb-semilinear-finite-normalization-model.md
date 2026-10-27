## Worker report

The module `Sheaf.AlgebraicGeometry.SemilinearFiniteNormalizationModel` states
`AlgebraicGeometry.semilinear_finite_normalization_model` with one `sorry`. It introduces
no new definitions, no new DAG nodes, and no dependency modules. The item's natural-language
statement and all its other fields remain unchanged; only `lean` is added.

Source read: Stacks `morphisms.tex`, definition-normalization-X-in-Y (035H),
lemma-characterize-normalization (035I), and `varieties.tex`, lemma-normalize-projective
(0GK4). The node's seven-step argument supplies the semilinear assembly. The theorem docstring
records every step, including normalization, finiteness, surjectivity, projectivity,
localization of the generic fibre, twisted-target descent, action laws and uniqueness.

The correspondence with every hypothesis is:

- A field `k`: `(k : Type u) [Field k]`.
- An integral projective finite-type `k`-scheme: `(S : Scheme.{u}) [IsIntegral S]`, its
  specified structure map `(p : S ⟶ Spec (.of k))`, and `[IsHProjective p]`,
  `[LocallyOfFiniteType p] [QuasiCompact p]`. H-projectivity is exactly the required finite
  projective-space embedding convention. No action on a projective embedding is required.
- `K = k(S)`: the existing generic-stalk carrier `S.functionField`, rather than a separate
  field or an arbitrary identification.
- A finite field extension `M/K`: `(M : Type u) [Field M] [Algebra S.functionField M]`
  and `[Module.Finite S.functionField M]`, with its specified `algebraMap` inclusion.
- A finite group acting on `S` and `k`: `(J : Type v) [Group J] [Finite J]`,
  `(h : J →* Aut S)` and `(σk : J →* (k ≃+* k))`.
- Compatibility with the structure map: `hscalar` says
  `(h j).hom ≫ p = p ≫ Spec.map (CommRingCat.ofHom (σk j⁻¹).toRingHom)`.
  The inverse converts the left field action to the geometric action of `Spec k`.
- The homomorphism `σ : J → Aut(M)` is `(σ : J →* (M ≃+* M))`.
- Its restriction is `(h_(j⁻¹))^*`: `hgeneric` states, for every `z : S.functionField`,
  `σ j (algebraMap _ _ z) = algebraMap _ _ ((Scheme.functionFieldAut (h j⁻¹)).hom z)`.
  The read upstream definition `functionFieldAut` uses precisely the generic stalk map,
  with the canonical stalk transport at the fixed generic point. It is not a chosen map.

The correspondence with every conclusion is:

- `B` and `u` are the fixed existing constructions `S.normalizationIn M` and
  `S.fromNormalizationIn M`, never existential substitute models.
- Integral: `IsIntegral (S.normalizationIn M)`.
- Normal, in the statement's explicit sense: the conjunction `IsDomain` and
  `IsIntegrallyClosed` for every local stalk of this very scheme.
- Projective finite type over `k`: `IsHProjective (S.fromNormalizationIn M ≫ p)`,
  `LocallyOfFiniteType` and `QuasiCompact` of that same composite.
- Finite and surjective: `IsFinite (S.fromNormalizationIn M)` and
  `Surjective (S.fromNormalizationIn M)`.
- The canonical `η_B` is `(S.fromSpecOfAlgebraFunctionField M).toNormalization`.
  The existential `ξ` is a generic point (`IsGenericPoint ξ Set.univ`) and is the image of
  `IsLocalRing.closedPoint M` under this map. `IsIso` of this map's `residueFieldMap` says
  exactly that it identifies the generic residue field (the function field of the integral
  normalization) with the source residue field, canonically identified with `M`.
- Generic fibre equals `Spec M`: `IsPullback η_B (Spec.map (CommRingCat.ofHom
  (algebraMap S.functionField M))) (S.fromNormalizationIn M) S.fromSpecFunctionField`.
  This states the universal property of the fibre product with the actual two canonical
  projections. It is the canonical identification, not merely a bare isomorphism of schemes.
- Unique lifted action: `∃! a : J →* Aut (S.normalizationIn M), ∀ j : J, ...`.
  The first equation is `(a j).hom ≫ u = u ≫ (h j).hom`, exactly `u a_j = h_j u`.
  The second is `η_B ≫ (a j).hom = Spec.map (CommRingCat.ofHom
  (σ j⁻¹).toRingHom) ≫ η_B`, exactly `a_j η_B = η_B Spec(σ_j⁻¹)` since `σ` is a group
  homomorphism. The final equation is compatibility with the specified action on `k` for
  the structure map `u ≫ p`. It follows from the two scalar/equivariance squares but is
  retained because it is an explicit conclusion of the node.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  Mathlib.AlgebraicGeometry.Properties.
- `def-kun-projective`: `AlgebraicGeometry.IsHProjective`,
  WeilConjectures.AlgebraicGeometry.Morphisms.Projective.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType and
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `def-sc-function-field`: WeilConjectures.AlgebraicGeometry.FunctionField explicitly
  delegates its arbitrary integral-scheme clause to Mathlib's `Scheme.functionField`.
  The general component-product definition is not the carrier used for this clause.
- `def-pc-field-extension`: `Algebra` and `algebraMap`, Mathlib.Algebra.Algebra.Defs.
- `def-fin-normalization-extension`: `Scheme.normalizationIn`,
  `Scheme.fromNormalizationIn`, `Scheme.fromSpecOfAlgebraFunctionField`,
  WeilConjectures.Mathlib.AlgebraicGeometry.Normalization. The canonical generic map is
  Mathlib's `Scheme.Hom.toNormalization` for that specified composite.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` and `IsIntegralHom`,
  Mathlib.AlgebraicGeometry.Morphisms.Finite and Integral.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`,
  Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap.
- `def-pc-fibre-product`: the recorded pullback universal property, represented by
  `CategoryTheory.IsPullback` for the canonical square; Mathlib.AlgebraicGeometry.Pullbacks
  supplies scheme pullbacks. This is equivalent to the recorded chosen `Limits.pullback`
  with both projection identifications, and avoids introducing an arbitrary isomorphism.

Additional existing construction read: `Scheme.functionFieldAut` in
WeilConjectures.AlgebraicGeometry.StalkAut, including its defining `stalkAut` and the
`SpecMap_functionFieldAut_hom_fromSpecFunctionField` compatibility. Its ordinary ring
isomorphism permits movement of `k`. The proof dependency modules, when recorded, are
imported privately: FiniteOverProjective, ProjectiveSpace, normalization-in-residue-field-
extension, and the Mathlib modules for relative normalization, finite type, proper and
finite morphisms, affine scheme pullbacks, and localization of integral closure.

Edge cases checked before writing: `S = Spec k` gives the ordinary finite field extension
model. `M = K` allows a nonnormal `S`; the normalization is not incorrectly replaced by
`S`. Purely inseparable extensions are included, with no separability hypothesis.
The trivial group and nonfaithful actions are allowed; there is no injectivity condition
on any homomorphism. Positive characteristic and scalar actions such as finite-field
Frobenius are allowed. Empty schemes are excluded by the node's integral hypothesis,
not by a new assumption. No dimension or projective linearization is imposed. `J` has
independent universe `v`; the scheme, ground field and extension share the library's
arbitrary ambient universe `u`, which can always be chosen to contain them together.

Searches actually run (2026-10-24):

- msearch LeanFinder: “A finite group action on a projective integral scheme and a
  compatible finite extension of its function field extends uniquely to its normalization,
  allowing semilinear automorphisms”. Eight hits, mainly Galois/integral-closure action
  theorems; none states the projective normalization theorem with semilinear scheme action.
- msearch Loogle: `"normalization", "map"`. Three hits: polynomial integral normalization,
  `Scheme.Hom.normalizationDiagramMap` and its coequifibered property; no match.
- msearch grep in Mathlib/AlgebraicGeometry:
  `normalization.*(map|[Aa]ut|[Aa]ction|[Ff]inite)|([Aa]ut|[Aa]ction).*normalization`.
  Nine chart/construction or Zariski-main hits; no matching theorem.
- msearch LeanSearch: “A group of semilinear automorphisms of a projective integral scheme
  and its finite function field extension acts uniquely on the finite normalization model”.
  Eight hits, including field Galois actions, projectivization action and
  `Scheme.Hom.instIsIsoToNormalizationOfIsIntegralHom`; no match.
- rg over lean/WeilConjectures and lean/Sheaf for `normalizationIn`, semilinear normalization,
  function-field automorphisms and maps, and the exact proposed declaration. Existing
  normalization and StalkAut interfaces were reused; no existing equivalent theorem.
  The consumer SemilinearGaloisAlterationDomination states a larger different theorem.
- rg for the exact node id in lean/WeilConjectures found no tagged declaration.
  rg in dag/lean_names_upstream.json also found no matching theorem name.

No statement fault or disputed claim was found. No dependency interface repair is needed.
The server `scompile.py` checked both sandbox and library module modes successfully with
no errors or warnings. The only postponed proof is the named theorem of this DAG node.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
