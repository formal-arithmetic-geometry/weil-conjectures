## Worker report

The module `Sheaf.AlgebraicGeometry.TraitAffineGenericAffinizationLocus` states
`AlgebraicGeometry.trait_affine_generic_affinization_locus`, with its only proof
`sorry`. It uses existing constructions throughout. No definitions, new nodes,
dependency repairs, or statement corrections are needed. The node copy changes
only `lean`. Its theorem docstring preserves all eleven proof steps and names
their dependencies; no proof is supplied in stage 2.

The source was read in the primary online scan of BLR, Néron Models, §6.5,
printed pp.161–162 (PDF pp.167–168):
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf
Lemma 6 supplies a principal affine locus meeting a nonempty special fibre, and
the proof of Theorem 1 identifies the quasi-finite locus and applies Zariski Main
to obtain the open immersion. The node records this geometric argument without
requiring a descent datum; the Lean adds no such datum.

Hypotheses and objects, matched individually:

- DVR: `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`.
  The existing DVR class is a local principal ideal ring with nonzero maximal
  ideal; together with `IsDomain` it is precisely the node's DVR.
- Fraction field: `FractionRing R`, the localization at the non-zero-divisors,
  which for a domain are exactly the nonzero elements. The generic base map is
  `Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))`.
- Residue field: `IsLocalRing.ResidueField R` is definitionally the quotient by
  the maximal ideal; its base map is
  `Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))`.
- Base: `Spec (.of R)` is the node's `T`.
- Scheme over the base: `(Y : Scheme.{u}) (f : Y ⟶ Spec (.of R))`.
- Smoothness: `[Smooth f]`, the node's recorded Mathlib notion.
- Separatedness: `[IsSeparated f]`, whose field is that `pullback.diagonal f`
  is a closed immersion. This is exactly the specified diagonal condition.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, the two parts of the
  node's finite-type definition. There is no additional finite-presentation,
  affine, normality, nonemptiness, or Noetherian hypothesis.
- Affine generic fibre: `hGeneric : IsAffine (pullback (C := Scheme.{u}) f
  (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))`.
- Global section ring and canonical map: `Y.toSpecΓ` has type
  `Y ⟶ Spec Γ(Y, ⊤)` and is the unit of `ΓSpec.adjunction`. It corresponds to
  the identity on `A = Γ(Y, ⊤)`. Thus the statement does not quantify over an
  arbitrary morphism in place of the canonical map. The structure map from
  `Spec A` to `T` is induced by
  `(Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop`; adjunction naturality makes
  `Y.toSpecΓ` the canonical `T`-morphism. No additional commutativity assumption
  is needed to specify that morphism.

Conclusions, matched individually:

- `IsSeparated Y.toSpecΓ`: the affinization is separated.
- `LocallyOfFiniteType Y.toSpecΓ ∧ QuasiCompact Y.toSpecΓ`: it is of finite type.
- `∃ W : Y.Opens`: the locus is represented by an open subscheme of `Y`.
- `∀ y : Y, y ∈ W ↔ Y.toSpecΓ.IsQuasiFiniteAtPoint y`: it is exactly the
  quasi-finite locus in `pqf-def-quasifinite`, including that predicate's local
  finite-type requirement. This uniquely determines `W` as an open set; no
  arbitrary choice of a smaller open can satisfy the statement.
- `IsCompact (W : Set Y)`: this open is quasi-compact.
- `(pullback.fst f (Spec.map (CommRingCat.ofHom
  (algebraMap R (FractionRing R))))) ⁻¹ᵁ W = ⊤`: the inverse-image open in
  `Y_F` is the entire generic fibre. Base change of the open inclusion
  identifies `W_F` with this inverse-image open subscheme, so this states the
  specified equality `W_F = Y_F`, with their scheme structures.
- `IsOpenImmersion (W.ι ≫ Y.toSpecΓ)`: the restriction of the actual canonical
  affinization to `W` is an open immersion into `Spec A`.
- `W.toScheme.IsQuasiAffine`: the requested quasi-affineness. Mathlib's
  `Scheme.IsQuasiAffine` includes quasi-compactness and makes the canonical
  map to its affine spectrum an open immersion, hence is equivalent to a
  quasi-compact open embedding in an affine scheme. The preceding conjuncts
  also exhibit exactly such an embedding into the specified `Spec A`.
- `Nonempty (pullback (C := Scheme.{u}) f (Spec.map
  (CommRingCat.ofHom (IsLocalRing.residue R)))) → Nonempty (pullback
  (C := Scheme.{u}) (W.ι ≫ f) (Spec.map
  (CommRingCat.ofHom (IsLocalRing.residue R))))`: nonempty special fibre of
  `Y` implies nonempty special fibre of `W`. These are scheme-theoretic
  pullbacks along the residue-field quotient map. There is no componentwise
  density clause, group law, or descent datum.

Dependency declarations read and reused:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, through `IsSeparated`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`,
  whose recorded convention for scheme base change is `Limits.pullback f T.hom`,
  with `pullback.fst` and `pullback.snd`. The recorded
  `Scheme.Modules.moduleBaseChange` is specifically for modules and is not used
  as a replacement for scheme base change.
- `lem-weil-pbc-morphism-into-affine-scheme`: `AlgebraicGeometry.ΓSpec.adjunction`,
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`; the same file's
  `Scheme.toSpecΓ` is precisely its unit at `Y`.
- `pqf-def-quasifinite`: `Scheme.Hom.IsQuasiFiniteAtPoint`,
  `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`. Its full affine-chart
  signature was read; it includes finite type, unlike bare Mathlib
  `Scheme.Hom.QuasiFiniteAt` without a finite-type hypothesis.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-nagata-quasi-affine-morphism`: the recorded owning module
  `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine` is imported publicly.
  Its `IsQuasiAffineHom` is the relative notion in the dependency; for the item's
  absolute assertion use the existing `Scheme.IsQuasiAffine` from its public
  import `Mathlib.AlgebraicGeometry.QuasiAffine`. There is no second definition.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType`, `QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.

All available proof-dependency modules are plain imports, whereas the statement
modules are public imports. At reading time the following proof dependencies
had no recorded Lean declaration or Mathlib match, so there is no module to
import for them yet: `lem-sfb-qcqs-functions-local-comparison`,
`lem-sfb-dedekind-smooth-fibre-dense-affine`, `lem-sfb-smooth-normal-ascent`.
They are not prerequisites for typing this statement, and their proof steps
remain explicitly recorded in the docstring and unchanged DAG.

Edge cases checked before writing:

- `Y = ∅`: its global section ring is the zero ring, its spectrum is empty,
  `W = ∅`, and both pullback fibres are empty. The generic inverse-image equality
  remains an equality of the unique open sets of the empty scheme.
- Empty special fibre: the last conclusion is an implication, so nothing
  requires a special-fibre point. For example, `Y = Spec (FractionRing R)` over
  the trait has empty special fibre; no surjectivity assumption excludes it.
- Nonempty special fibre: only its nonemptiness, not meeting every component,
  is asserted for `W`; the BLR warning about componentwise density is respected.
- Empty generic fibre is allowed by the signature; smoothness and flatness over
  a trait force any such source to be empty, and the previous empty case applies.
- The zero ring is excluded for `R` by `IsDomain`, as a DVR requires; it is
  allowed for `Γ(Y, ⊤)`. No characteristic or dimension of `Y` is restricted.
- Every binder and universe is explicit (`set_option autoImplicit false`).
  All schemes and both canonical fields live in the common universe `u`;
  there is no quantification over tests in a possibly smaller universe.

Searches for existing declarations (via the prescribed `msearch.py Q90
lem-sfb-trait-affine-generic-affinization-locus` wrapper):

1. `leanfinder`, query: "The quasi finite locus of the canonical affinization of a
   smooth separated finite type scheme over a discrete valuation ring with affine
   generic fibre is quasi affine and meets the special fibre". Eight hits included
   `Scheme.IsQuasiAffine`, `Scheme.instIsQuasiAffineOfIsAffine`, and
   `LocallyQuasiFinite.quasiFinite_appLE`; none states this theorem.
2. `leansearch`, query: "The quasi-finite locus of the affinization of a smooth
   separated finite type scheme over a discrete valuation ring with affine generic
   fibre is quasi-affine". Eight hits included `Scheme.IsQuasiAffine`,
   `Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen`, and ring-level
   `Algebra.QuasiFiniteAt`; none is this statement.
3. `loogle`, query: "AlgebraicGeometry.Scheme.toSpecΓ,
   AlgebraicGeometry.IsQuasiAffine". Zero hits, because the latter name is not
   qualified through `Scheme`. Corrected query: "AlgebraicGeometry.Scheme.toSpecΓ".
   Twelve hits, including `Scheme.toSpecΓ`, `ΓSpec.adjunction_unit_app`,
   `Scheme.toSpecΓ_naturality`, and `Scheme.toSpecΓ_appTop`; use the existing unit.
4. `grep`, query `toSpecΓ|quasiFiniteLocus`, subdirectory `AlgebraicGeometry`.
   Twenty-five displayed hits include the canonical map and quasi-affine class.
   Direct `rg` additionally located `Scheme.Hom.quasiFiniteLocus` and
   `Scheme.Hom.isOpen_quasiFiniteAt` in `ZariskisMainTheorem.lean`.
   The theorem specifies an existential open by the exact point predicate, so it
   does not introduce another locus construction or require an unproved
   finite-type instance merely to type that open.
5. `rg` in the prescribed `lean/WeilConjectures` and `lean/Sheaf` directories:
   `affinization|trait_affine_generic|trait-affine-generic|IsQuasiFiniteAtPoint`
   found related affinization and quasi-finiteness modules, not this result.
   More focused `trait.*affini|affini.*trait|toSpecΓ.*IsQuasiFiniteAtPoint|
   IsQuasiFiniteAtPoint.*toSpecΓ` found no match before creating the file.
   Searching the exact node id and the proposed declaration name in both roots
   also found no match. No existing theorem covers every clause.

Validation: `scompile.py` compiled the module both as a sandbox file and at its
library module path against the live published build (1.8 s for each). No errors
or unexpected warnings remained. An initial type-inference failure under
`Nonempty` was repaired by explicitly selecting `(C := Scheme.{u})` for scheme
pullbacks; no assumption or conclusion changed.

## Second reading by Q90

This is the author's separate second pass, not an independently delegated review:
the dispatcher explicitly prohibits starting another agent. The delivery is
submitted for the maintainer's independent reading.

Reopened the node and module and checked each of the four geometric hypotheses,
the concrete fraction/residue fields, and every conclusion against the signature.
The exact-locus biconditional prevents replacing `W` by an arbitrary quasi-affine
open. The equality is on the inverse-image open of the generic pullback, hence
identifies the open subschemes with their scheme structures, not merely their
point sets. The last pullback uses the structure morphism `W.ι ≫ f` and the
residue quotient; it does not assert nonemptiness of `W` alone. The canonical
map is the adjunction unit and is never an unconstrained map. The absolute
quasi-affine predicate includes quasi-compactness. The empty source and empty
special-fibre cases remain included. No mathematical mismatch was found; the
only correction during compilation was the explicit category argument noted
above. No definition or node statement was changed.
