## Worker report

The module `Sheaf.AlgebraicGeometry.AffinePushforwardQuasiCoherentQuotient` states
`AlgebraicGeometry.Scheme.Modules.affine_pushforward_quasiCoherent_quotient`.
It has one theorem, whose entire proof is `sorry`, and no new definitions.
Only the item's `lean` field changes. No statement correction is needed.

Hypothesis and conclusion correspondence:

- Schemes and their affine morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)
  [IsAffineHom f]`. The universe is explicit; there are no additional finiteness,
  separatedness, nonemptiness or affineness hypotheses on X or Y.
- The subsheaf K of H is represented by `{K H : X.Modules} (i : K ⟶ H)
  [Mono i]`. A monomorphism represents a subobject, without choosing a particular
  set-theoretic realization. Mono gives sectionwise injectivity in this category.
- Both modules are quasi-coherent: `[K.IsQuasicoherent] [H.IsQuasicoherent]`.
  No finite-type or coherence hypothesis is imposed.
- The specified quotient and its map: `{Q : X.Modules} (q : H ⟶ Q)` together
  with `hiq : i ≫ q = 0` and `IsColimit (CokernelCofork.ofπ q hiq)`.
  This says precisely that q is a cokernel of the subsheaf inclusion. Module-sheaf
  cokernels are sheafified sectionwise quotients. Q is arbitrary, and is not
  assumed quasi-coherent in advance. The cocone proof is the quotient universal
  property already included in the node, not an added exactness assumption.
- Q and the three direct images are quasi-coherent: the first four conjuncts,
  `Q.IsQuasicoherent` and `((pushforward f).obj M).IsQuasicoherent`
  for M = K, H, Q.
- Short exactness of the pushed sequence:
  `((ShortComplex.mk i q hiq).map (pushforward f)).ShortExact`.
  ShortExact includes monicity of the pushed inclusion, exactness in the middle,
  and epimorphicity of the pushed quotient map. It does not mean surjectivity
  on every open, which would be false in general.
- Surjectivity on every affine open U of Y and its specified kernel:
  `∀ U : Y.Opens, IsAffineOpen U → Function.Surjective (q.app (f ⁻¹ᵁ U)) ∧ ...`.
  The second conjunct is equality of the linear-map kernel of q with the range
  of i on this inverse image. Since i is injective, its range is precisely the
  included copy of K's sections.
- On every open U, the pushed quotient's kernel is the pushed subsheaf:
  `∀ U : Y.Opens, LinearMap.ker (((pushforward f).map q).val.app (op U)).hom =
  LinearMap.range (((pushforward f).map i).val.app (op U)).hom`.
  These are submodules over the structure ring of Y on U. On the affine inverse
  image formula the submodules instead use the structure ring of X there.
- The quotient after pushforward is `cokernel ((pushforward f).map i)` and its
  projection is `cokernel.π ((pushforward f).map i)`; these are existing Mathlib
  constructions. The existential θ is an isomorphism to `(pushforward f).obj Q`,
  with `cokernel.π ... ≫ θ.hom = (pushforward f).map q`.
- Uniqueness: every isomorphism θ' with that same projection relation equals θ.
  Existence and the cokernel projection's epimorphicity characterize the canonical
  morphism as well; the theorem does not posit arbitrary comparison data.
- Naturality: quantify a second quasi-coherent pair `(H',K')`, any quotient q'
  with its cokernel universal property, and a morphism of pairs `(a,b)` satisfying
  `i ≫ a = b ≫ i'`. The induced quotient arrows aQ and aP are characterized by
  `q ≫ aQ = a ≫ q'` and `cokernel.π ... ≫ aP = (pushforward f).map a ≫
  cokernel.π ...`, respectively. For every target comparison θ' with the defining
  projection relation the conclusion is `aP ≫ θ'.hom = θ.hom ≫ (pushforward f).map aQ`.
  The universal properties ensure these induced arrows exist uniquely, so the
  quantification covers the actual canonical induced arrows, with no free-map
  or noncanonical-choice hypothesis.

Recorded dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`; imported transitively by the affine-morphism module.
- `pqf-def-affine-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `AlgebraicGeometry.IsAffineHom`, imported publicly.
- `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`,
  imported publicly. Its abbreviation is exactly `SheafOfModules`; `X.Modules`
  is Mathlib's same category for `X.ringCatSheaf`, with its canonical abelian instance.
  No second category or instance is constructed.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, imported
  publicly for its exposed `SheafOfModules.IsQuasicoherent`. The conjunction
  IsQuasiCoherentFiniteType would add a hypothesis and is deliberately not used.

Available proof-dependency modules are imported without `public`:
`WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
(`Scheme.Modules.quasiCoherent_cokernel_image`),
`WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs`
(`Scheme.Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated`),
`WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover`
(`Scheme.Modules.Hom.isIso_of_bijective_on_affine_open_cover`),
`Mathlib.CategoryTheory.Sites.Sheafification` (`presheafToSheaf`,
`toSheafify`, `sheafificationAdjunction`), and
`Mathlib.AlgebraicGeometry.Morphisms.Separated` for affine separatedness.
The remaining affine permanence facts are in the public affine import.

Source checked directly: `literature/stacks-project/divisors.tex`,
`lemma-strict-transform-affine` (Tag 080G), whose proof concludes by exactness
of affine direct image; `schemes.tex`, `lemma-equivalence-quasi-coherent`
(Tag 01IB), and `lemma-kernel-cokernel-quasi-coherent` (Tag 01IC).
The theorem docstring gives all five node proof steps and their dependency IDs.

Edge cases checked by reading the statement and the affine-module argument:
empty schemes and empty opens are allowed; there is no Nonempty hypothesis;
K = 0 gives the identity quotient comparison, K = H gives a zero quotient,
and zero H forces zero K. The identity morphism is included. For a general
non-affine open the statement asserts only the kernel formula, not surjectivity.
No characteristic, rank, dimension, or Noetherian restriction appears. Universes
are explicit and use Mathlib's scheme-module size convention. Naturality includes
identity and zero morphisms of pairs, and arbitrary realizations of both quotients.

Searches (all through the prescribed msearch.py wrapper, Q58 and this item):

- LeanFinder: `Affine pushforward of quasi coherent module sheaves preserves
  quotients canonically and is exact`. Eight hits, including Modules.pushforward,
  instAdditivePushforward, instAbelian, instIsRightAdjointPushforward, and generic
  SheafOfModules pushforward constructions. No theorem states these clauses.
- Loogle: `AlgebraicGeometry.Scheme.Modules.pushforward`. Twelve hits, including
  pushforward, its adjunctions, open-immersion full/faithful instances, and
  composition/identity isomorphisms. No full match.
- LeanSearch: `Affine direct image of quasi coherent module sheaves preserves
  quotients and short exact sequences`. Eight hits, including additive pushforward,
  quasi-coherence definitions, and affine base-change stability. No full match.
- Mathlib grep: `(exact|Exact|cokernel|Cokernel|quotient|Quotient).*pushforward|pushforward.*(exact|Exact|cokernel|Cokernel|quotient|Quotient)`
  in AlgebraicGeometry. Four hits in Modules/Sheaf and Modules/Tilde, concerning
  other constructions and open-immersion preservation. No full match.
- The same rg search in `lean/WeilConjectures` and `lean/Sheaf` found related
  exactness/cohomology/closed-immersion results, but no statement of this quotient
  theorem. Searching the item ID in WeilConjectures found no binding. Searching
  the proposed declaration name in Mathlib, both project roots, and
  `dag/lean_names_upstream.json` found no collision.
- Read Mathlib's `cokernelComparison` and its naturality in
  CategoryTheory/Limits/Shapes/Kernels.lean. This is a generic comparison with
  the chosen cokernel before pushforward; it does not assert that the map is an
  isomorphism for these modules, and does not give the other required clauses.
  Existing cokernels and their universal properties are reused directly.

Validation: scompile.py compiled this single file separately in sandbox and
library modes against the published server library; both succeeded in 3.9 s
without warnings. The only postponed proof is the named theorem above.

## Second reading by Q58

The dispatcher forbids starting other agents; this is a separate self-review
with the node and final source open, not a claim of an independent agent review.
The maintainer performs the independent delivery review.

I matched the four quasi-coherence conclusions with the first four conjuncts,
then checked that ShortExact is the full mono/exact/epi condition, rather than
only sectionwise middle exactness. I checked the two section formulas separately:
one is over X's inverse image and requires affine U, the other is over all opens
of Y. The arbitrary cokernel Q avoids restricting q to a chosen representative.
I checked composition order in both the factorization and naturality equations:
Lean writes composition left to right, so π ≫ θ is θ composed with π in the node.
Uniqueness compares isomorphisms with the same factorization, while the last
quantified clause relates θ to any target comparison satisfying its factorization.
Every induced arrow is constrained by the corresponding quotient commuting square.
The K'/H' quasi-coherence assumptions restrict only the second pair in naturality,
not the original theorem. No premise assumes the quasi-coherence of Q or Q'.
No mismatch or statement correction was found. No auxiliary definition or theorem,
new node, dependency record change, private notation, or local instance is present.
