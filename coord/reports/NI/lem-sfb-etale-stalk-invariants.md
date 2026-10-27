## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleStalkInvariants` states
`AlgebraicGeometry.etale_stalk_invariants`, with its entire proof `sorry`.
It introduces no definitions. The node is unchanged except for its `lean` record.
Its six proof steps are transcribed into the theorem docstring, including the
base change before smooth ascent that avoids treating a stalk map as a finitely
presented étale ring map.

Hypotheses and conclusions, clause by clause:

- Arbitrary schemes U and X are `{U X : Scheme.{u}}`, with `universe u` explicitly
  declared. The morphism is `(e : U ⟶ X)` and its étaleness is `[Etale e]`.
- The point u is `(u : U)`. The image point x is written `e u` everywhere.
  The specified rings A and B are exactly `X.presheaf.stalk (e u)` and
  `U.presheaf.stalk u`. There are no independently chosen rings or identifications.
- The actual local homomorphism A -> B is `(e.stalkMap u).hom`.
  `Scheme.Hom.stalkMap` has exactly these source and target rings, and
  `Scheme.Hom` already supplies its `IsLocalHom` instance. This is not an
  arbitrary comparison map or an extra locality assumption.
- Faithful flatness is the first conjunct, `(e.stalkMap u).hom.FaithfullyFlat`.
  `RingHom.FaithfullyFlat` installs this very map's algebra structure and uses
  `Module.FaithfullyFlat`, the recorded dependency's ring-map notion.
- Dimension equality is the second conjunct,
  `ringKrullDim (X.presheaf.stalk (e u)) = ringKrullDim (U.presheaf.stalk u)`.
  Its values lie in `WithBot ℕ∞`, so infinite dimensions are retained.
- Regularity is the third conjunct, an equivalence between
  `IsRegularLocalRing` of A and of B. This predicate itself includes both locality
  and Noetherianity; no Noetherian hypothesis is assumed beforehand.
- The fourth conjunct is the equivalence
  `(IsDomain A ∧ IsIntegrallyClosed A) ↔ (IsDomain B ∧ IsIntegrallyClosed B)`,
  expanded using the two actual stalk types. Both domain and integral-closure
  clauses occur on each side, as prescribed by the normal-ring node's record.
- There is no global Noetherian, local Noetherian, finite-dimension, domain,
  regularity, residue-field-isomorphism, or fraction-field-isomorphism hypothesis.
  No field comparison is asserted. The negative explanatory clauses in the node
  are also stated explicitly in the docstring.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`:
  its affine-section class and its flat/formally-unramified/finite-presentation
  characterization. This is the recorded `def-weil-etale-morphism` declaration.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, `Module.FaithfullyFlat`, and
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`, `RingHom.FaithfullyFlat`:
  faithfully flat module and actual ring-map specialization recorded by
  `def-weil-pbc-faithfully-flat-ring-map`. The public ring-map import exports the
  module predicate as well.
- `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`:
  the recorded `def-weil-pbc-krull-dimension-ring` declaration.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`,
  whose public upstream regular-scheme import exports
  `Mathlib.RingTheory.RegularLocalRing.Defs.IsRegularLocalRing` (the declaration's
  full name is simply `IsRegularLocalRing`). The item uses the ring clause of
  `def-weil-regular-scheme`, supplied by that node's unchanged `mathlib_match`,
  rather than imposing the scheme-wide `IsRegularScheme` condition.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`,
  together with `IsDomain`: these are the recorded normal-domain conjunction
  of `def-weil-pbc-normal-ring`. Its general normal-ring clause is not needed
  in the public signature; it is used in the proof plan.
- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom.stalkMap`:
  the canonical stalk map and its local-hom instance, already public through the
  étale-morphism import.

All recorded proof-dependency modules are imported. Imports used only by the
proof plan are non-public:

- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat.stalkMap`.
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`:
  `AlgebraicGeometry.LocallyRingedSpace.Hom` and its local stalk-map condition.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`:
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`.
- `Mathlib.AlgebraicGeometry.AffineScheme`:
  `AlgebraicGeometry.Spec.stalkIso` and
  `AlgebraicGeometry.Scheme.localRingHom_comp_stalkIso`.
- `WeilConjectures.RingTheory.Etale.LocalDimension`:
  `RingHom.Etale.ringKrullDim_localization_eq`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange`:
  `AlgebraicGeometry.Scheme.finite_affine_tensor_base_change`.
- `Mathlib.CategoryTheory.Limits.MorphismProperty`: finite limits and their
  pullback preservation, with étale base change from the public étale import.
- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`:
  `AlgebraicGeometry.HasRingHomProperty.Spec_iff`.
- `Mathlib.RingTheory.Smooth.Basic`: `Algebra.Smooth`.
- `WeilConjectures.RingTheory.RegularLocalLocalization`:
  `IsRegularLocalRing.localization_at_prime_and_isRegularRing`.
- `WeilConjectures.RingTheory.RegularRingSmoothAscent`:
  `Algebra.isRegularRing_of_smooth`.
- `WeilConjectures.RingTheory.LocalizationOfRegularRing`:
  `RingTheory.isRegularRing_of_localization`.
- `WeilConjectures.RingTheory.RegularRingFaithfullyFlatDescent`:
  `IsRegularRing.of_faithfullyFlat`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` (already public):
  `isIntegrallyClosed_of_isLocalization` for localization of normal domains.
- `WeilConjectures.RingTheory.EtaleNormalRing`: `RingHom.Etale.isNormalRing`.
- `Sheaf.RingTheory.FaithfullyFlatNormalRingDescent`:
  `Algebra.normal_ring_of_faithfullyFlat`.

Sources checked directly: Stacks `more-algebra.tex`, labels
`lemma-dimension-etale-extension` (07QP) and `lemma-regular-etale-extension`
(0AH0); `algebra.tex`, labels `lemma-normal-goes-up` (033C) and
`lemma-descent-normal` (033G). Dimension and regularity are exactly the
localization results. Normality ascent applies after the base-local-ring
base change to the étale algebra, followed by localization; descent applies
to the faithfully flat local stalk map. No hidden Noetherian assumption occurs.

Edge cases checked before writing:

- Identity maps on arbitrary schemes give the identity local homomorphism and
  reflexive dimension, regularity, and normal-domain comparisons, including
  singular and non-Noetherian schemes.
- An empty source has no point u, so the assertion is vacuous. No point of a
  scheme has zero stalk ring, since scheme stalks are nontrivial local rings.
- A finite separable extension of fields yields dimension zero and both local
  predicates, while its residue and fraction fields can differ; the signature
  makes no incorrect field-isomorphism claim.
- Infinite Krull dimension is allowed by `WithBot ℕ∞`. Neither regularity nor
  normality is assumed in order to state the dimension assertion.
- Reducible or disconnected schemes are allowed. The intermediate étale algebra
  can be a product; the normality proof uses normal rings before taking its
  local ring, and never assumes that intermediate algebra is a domain.
- The explicitly declared universe is arbitrary, and there are no test-object
  quantifiers with smaller or vacuous universes. Every binder is explicit and
  `autoImplicit` is false.

Searches for existing declarations:

- `msearch.py ... leanfinder "An etale morphism induces faithfully flat maps on
  local rings, preserves their Krull dimension, and reflects regularity and
  normality."`: eight hits, including `RingHom.Etale.propertyIsLocal`, the étale
  scheme predicate and smoothness/formally-unramified instances, and étale
  localization lemmas. None states the four-clause stalk package.
- `msearch.py ... loogle '"Etale", "stalkMap"'`: zero hits.
- `msearch.py ... grep 'Etale.*(IsRegularLocalRing|IsIntegrallyClosed|ringKrullDim)|
  (IsRegularLocalRing|IsIntegrallyClosed|ringKrullDim).*Etale'`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for étale stalk invariants,
  stalk regularity/integral-closure equivalences, and stalk dimension found
  related one-direction regularity and unrelated local-dimension statements,
  but no full statement. In particular the upstream
  `AlgebraicGeometry.isRegularLocalRing_stalk_of_etale` assumes a regular target
  scheme and only proves one direction; it cannot represent this node.
- `rg -n 'lem-sfb-etale-stalk-invariants' lean/WeilConjectures`: no hits.
  The project hits in `VeryTameBoundaryQuotientCartier` and
  `SchemeEtaleSourceTargetProperties` are citations in proof-plan docstrings,
  not declarations of this statement.
- Read the dependency nodes' recorded declarations and docstrings directly,
  including the existing regular-scheme dependency module and the Mathlib
  ring predicates. No private copies or new notions are needed.

No STATEMENT-DISPUTED issue, node fault, new node, dependency repair, or statement
correction was found.

Validation: `scompile.py NI lem-sfb-etale-stalk-invariants <module>` passed both
the sandbox-name compile (1.6 seconds) and library-name compile (1.5 seconds),
with no compiler errors or unexpected warnings. All delivered Lean lines have
at most 100 characters. The only postponed theorem is
`AlgebraicGeometry.etale_stalk_invariants`, matched to this DAG node.

## Second reading by NI

A second pass by the same worker reopened the node and final Lean file; no
separate agent was started, as required by the dispatcher brief. The maintainer
will perform the independent delivery review.

I checked the complete binder list against the first sentence: U, X, e,
étaleness, and u; x, A and B are expanded canonically rather than independently
quantified. The first conjunct names the actual ring homomorphism induced by
e, with the correct contravariant direction. The dimension clause has the
source local ring A on the left and B on the right. The regularity equivalence
uses precisely the Noetherian local-ring predicate on each stalk. The final
parenthesized equivalence includes both `IsDomain` and `IsIntegrallyClosed` on
each side; its parentheses keep it inside the conjunction, not an equivalence
between the entire preceding package and the B predicate. Neither a global
regularity/normality assertion nor a comparison of fields was inserted.

I reread the six-step proof docstring against the accepted proof: faithful
flatness, affine-local dimension, tensor base change before localization,
regularity ascent, regularity descent, then both directions of normality.
The proof imports include the existing faithfully-flat normal-ring descent
module. No mismatch or additional repair was found. The final recorded
signature is copied verbatim from the file, stopping before `:=`.
