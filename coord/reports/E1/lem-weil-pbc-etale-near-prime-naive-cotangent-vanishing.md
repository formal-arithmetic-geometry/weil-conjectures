## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleAwayOfLocalizedCotangentVanishing` states
`AlgebraicGeometry.exists_etale_away_of_localized_cotangent_vanishing`, with one `sorry`
and no definitions or proofs. The node is unchanged except for its `lean` record.
No new nodes, dependency modules, statement correction, or disputed statements are needed.

Hypotheses and conclusion matched clause by clause:

- Commutative rings A and C: `{A C : Type u} [CommRing A] [CommRing C]`.
  The universe `u` is arbitrary; both rings may be placed in a common universe, as required
  by the category of schemes containing both spectra. No size, finiteness of the underlying
  sets, or nontriviality condition is imposed.
- The homomorphism A → C: `[Algebra A C]`, whose map is `algebraMap A C`.
  This is the usual unbundled encoding of an arbitrary unital homomorphism, not an
  additional restriction on it.
- C finitely presented over A: `[Algebra.FinitePresentation A C]`.
- A prime ideal q of C: `(q : Ideal C) [q.IsPrime]`.
- H₁(L_{C/A}) localized at q is zero:
  `(hH : Subsingleton (LocalizedModule q.primeCompl (Algebra.H1Cotangent A C)))`.
  `Algebra.H1Cotangent` is the kernel in the canonical presentation indexed by C,
  exactly the naive first cotangent homology in the dependency node's match.
- Ω_{C/A} localized at q is zero:
  `(hΩ : Subsingleton (LocalizedModule q.primeCompl (KaehlerDifferential A C)))`.
  Localization is at the multiplicative complement of the prime. For either additive
  module, `Subsingleton` says every element equals zero, exactly vanishing.
- There is h in C outside q: `∃ h : C, h ∉ q ∧ ...`.
- The scheme map Spec C_h → Spec A induced by A → C → C_h is étale:
  `Etale (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away h))))`.
  The canonical A-algebra structure on the principal localization is the composite
  through C, so this is the particular morphism in the node, with no other map chosen.

Dependency declarations read and used:

- `def-weil-pbc-smooth-ring-map`: its Mathlib match is `Algebra.Smooth`,
  `Mathlib.RingTheory.Smooth.Basic`. Its recorded explanation explicitly identifies
  the canonical `Algebra.H1Cotangent A C` from
  `Mathlib.RingTheory.Extension.Cotangent.Basic` with the node's H₁. That homology
  is what the statement needs; no smoothness hypothesis is added. Read both the
  `Smooth`/`FormallySmooth` signatures and `H1Cotangent` signature/docstring.
- `def-weil-pbc-kahler-differentials`: `KaehlerDifferential`,
  `Mathlib.RingTheory.Kaehler.Basic`. Read its definition/docstring and the
  `D` and `linearMapEquivDerivation` declarations for its universal property.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`; read their signatures and docstrings.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`; read its definition and the affine
  ring-homomorphism-property instance. This is the scheme-level conclusion.

The two imports provide these declarations. `Mathlib.RingTheory.Etale.Locus` provides
cotangent homology, differentials and module localization through its imports;
`Mathlib.AlgebraicGeometry.Morphisms.Etale` provides the scheme map and étale property.
No dependency needs a private replacement. The docstring follows all four proof steps
and names their DAG dependencies, but the Lean proof remains `sorry` for stage 3.

Edge cases checked before writing:

- C the zero ring has no prime ideal, so the prime hypothesis excludes it for the same
  reason as the source; there is no added nontriviality hypothesis.
- A the zero ring permits only a zero target algebra, so again no prime case occurs.
- For the identity algebra or an étale algebra, both localizations vanish and h = 1
  gives the expected neighbourhood. The prime's properness guarantees 1 is outside q.
- Rank zero differentials are admitted, including an empty generator family in step 2
  (its product is 1). No positive rank hypothesis is imposed.
- Nilpotents in A or C, positive characteristic and non-Noetherian rings are admitted;
  finite presentation is the only finiteness hypothesis.
- h outside a prime cannot be nilpotent, hence the resulting basic open contains q.

Searches for an existing exact statement, performed with
`/home/ubuntu/weil-launcher/msearch.py E1` and this item id:

- LeanFinder: `finitely presented algebra with first cotangent homology and Kahler
  differentials zero at a prime has an etale principal localization`.
  Eight hits, including `Algebra.IsEtaleAt` and `Algebra.exists_etale_of_isEtaleAt`.
  The latter assumes formal étaleness of C_q, not the two localized-module hypotheses,
  and concludes ring-algebra étaleness; it is not this exact statement.
- Loogle: `Algebra.H1Cotangent, Algebra.Etale`. Zero hits.
- Mathlib grep: `exists_etale|H1Cotangent|Subsingleton.*LocalizedModule`, restricted
  to `RingTheory/Etale`. Eighteen hits; `etaleLocus_eq_compl_support` and
  `exists_etale_of_isEtaleAt` supply pieces, not a single declaration with this signature.
  Read `Mathlib.RingTheory.Etale.Locus` in full through its main results.
- LeanSearch: `vanishing localized cotangent homology and Kahler differentials implies
  existence of an etale localization`. Service unavailable (Internal Server Error).
- Local rg of `etale.*(cotangent|vanish)|exists_etale|LocalizedModule.*H1Cotangent|
  etale_near_prime` over source `WeilConjectures` and repository `lean/Sheaf`:
  neighbouring statements, notably `EtaleAtPrimeFlatUnramifiedCriterion`, but no exact
  theorem. Read that module; its first implication cites this item.
- `grep -rn` of the item id over source `WeilConjectures`: no hits.
- Declaration collision search of `exists_etale_away_of_localized_cotangent_vanishing`
  in `dag/lean_names_upstream.json`, Mathlib, source `WeilConjectures`, and `lean/Sheaf`:
  no hits.

Source verification: the local `literature/stacks-project` text files are absent on this
machine, so read the primary Stacks pages directly:
[07BU](https://stacks.math.columbia.edu/tag/07BU),
[07M7](https://stacks.math.columbia.edu/tag/07M7), and
[00U1](https://stacks.math.columbia.edu/tag/00U1).
The rank-zero specialization of 07BU and the étale conclusion used in the proof of 07M7
agree with the node. No correction is required.

Validation: remote single-file compilation and `deliver2.py --no-push`; the worker does
not push or write a second-reading section.

## Second reading by E1

I independently read the sandbox node and module, all four statement-dependency nodes,
and their Mathlib declarations. No semantic mismatch was found; the module and the
node's signature are preserved. Only this second-reading report is added. There are
no new definition nodes, dependency modules, or statement corrections to review.

Source reading: local Stacks .tex files are absent, so I read the upstream .tex directly
from `https://raw.githubusercontent.com/stacks/stacks-project/master/`: `algebra.tex`,
labels `lemma-smooth-at-point` (07BU), `definition-smooth-at-prime` (00TB), and
`definition-etale` (00U1); `more-algebra.tex`, label
`lemma-lift-section-smooth-morphism` (07M7); and `morphisms.tex`, label
`lemma-etale-characterize` (02GJ). I also checked the corresponding Stacks tag pages.
07BU assumes only finite presentation and a prime, with no Noetherian, field, or
characteristic hypothesis. Its rank-zero specialization and the cited paragraph of
07M7 give precisely the node's neighbourhood assertion; 00U1 and 02GJ give its
scheme-level conclusion. The ideal, smooth algebra, and section of 07M7 are objects
of its application, not extra hypotheses of the general 07BU consequence here.

The complete object/hypothesis/conclusion list and its Lean rendering:

1. Commutative rings A and C: `{A C : Type u} [CommRing A] [CommRing C]`.
   Verdict: exact. Arbitrary `u` allows all sizes in the common universe required by
   Mathlib's scheme category; rings of different initial sizes may be raised to a
   common universe. There is no `Nontrivial`, field, or Noetherian binder.
2. A unital ring map A → C: `[Algebra A C]`, rendered by `algebraMap A C`.
   Verdict: exact; every map of commutative rings induces this algebra structure.
3. C finitely presented as an A-algebra: `[Algebra.FinitePresentation A C]`.
   Verdict: exact; finite type alone would have been insufficient.
4. A prime ideal q of C: `(q : Ideal C) [q.IsPrime]`.
   Verdict: exact, including properness implicit in primality.
5. The canonical naive first cotangent homology localized at q vanishes:
   `hH : Subsingleton (LocalizedModule q.primeCompl (Algebra.H1Cotangent A C))`.
   Verdict: exact. `Generators.self` (Extension/Generators.lean:171) is the presentation
   with one variable for every element of C. `Extension.cotangentComplex` (:61 of
   Extension/Cotangent/Basic.lean) is I/I² → C ⊗ Ω, its `H1Cotangent` (:339) is
   the kernel, and `Algebra.H1Cotangent` (:561) takes this canonical presentation.
   This is the object defined in `def-weil-pbc-smooth-ring-map`, not a smoothness
   assumption or a different homology degree.
6. Kähler differentials localized at q vanish:
   `hΩ : Subsingleton (LocalizedModule q.primeCompl (KaehlerDifferential A C))`.
   Verdict: exact. `KaehlerDifferential` (Kaehler/Basic.lean:153), `D` (:198), and
   `linearMapEquivDerivation` (:327) realize the universal pair in
   `def-weil-pbc-kahler-differentials`. For both modules `Subsingleton` means zero,
   because they are additive groups. `q.primeCompl` is exactly localization at q.
7. There exists an element h of C outside q: `∃ h : C, h ∉ q ∧ ...`.
   Verdict: exact, with the witness chosen after both vanishing hypotheses.
8. The induced morphism Spec C_h → Spec A is étale:
   `Etale (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away h))))`.
   Verdict: exact. `Localization.Away h` is C_h; its A-algebra map is the composite
   through C. `Spec` and `Spec.map` (Scheme.lean:470,479) are the recorded affine
   spectrum notion. `Etale` (Morphisms/Etale.lean:41) tests affine ring maps;
   `Etale.iff_flat_and_formallyUnramified` (:140) supplies the dependency node's
   flat, unramified, locally finitely presented characterization. The conclusion
   selects no unrelated morphism and states scheme étaleness as requested.

The dependency nodes have usable Mathlib matches, though no `lean` records on this
base: no dependency replacement is necessary. In particular, the item uses the H₁
object named by the smooth-ring-map definition without assuming `Algebra.Smooth`.
The imported Etale/Locus module provides the localized modules and cotangent objects;
Morphisms/Etale provides the conclusion. Neither import is extraneous.

Edge cases: a zero C has no prime and hence no q; a zero A forces C zero for a unital
algebra, so its lack of primes is also faithful. Identity algebras satisfy both
vanishings and admit h = 1. A zero localized module is admitted without a nonzero
rank assumption. Empty finite generator families in proof step 2 have product 1;
n = 0 is allowed. No characteristic, reducedness, or Noetherian restriction occurs.
The basic neighbourhood contains q, so an empty spectrum cannot secretly supply the
conclusion for an existing prime. There are no free variables or universes.

Independent searches, using msearch with this group and item:

- LeanFinder: `localized first cotangent homology and differentials vanish implies
  etale neighborhood of prime`: eight hits, notably `Algebra.IsEtaleAt` and
  `Algebra.exists_etale_of_isEtaleAt`. I read Etale/Locus.lean:35–112: the latter
  starts with formal étaleness of the local ring and concludes ring étaleness;
  `etaleLocus_eq_compl_support` is a separate conversion. No exact replacement.
- Loogle: `Algebra.H1Cotangent, LocalizedModule`: zero hits.
- LeanSearch: `prime localization zero Kahler differentials and first cotangent
  homology etale neighborhood`: unavailable, Internal Server Error; not a negative
  search result.
- msearch grep: `H1Cotangent|etaleLocus_eq_compl_support|exists_etale_of_isEtaleAt`
  in `RingTheory/Etale/Locus.lean`: five displayed hits, the support conversion.
  Direct rg of `cotangent.*(etale|étale)|exists_etale|etale.*vanish|localized_cotangent`
  across source WeilConjectures, repository lean/Sheaf, and Mathlib RingTheory/Etale
  found related results but no exact statement. I opened the landed
  `EtaleAtPrimeFlatUnramifiedCriterion.lean`: it concerns local-ring étaleness versus
  flatness and unramifiedness and cites this item; it is not its replacement.
- Direct rg for the item id and declaration name in dag/lean_names_upstream.json,
  source WeilConjectures and lean/Sheaf found only that citing docstring and no
  declaration collision.

The theorem has only a `sorry` proof, no definitions or proved helpers. Its declaration
and module docstrings contain the source and blueprint id. I matched the declaration
proof docstring against all four node steps: smooth neighbourhood, finite-generator
annihilator and h = gc, smooth localization with vanishing differentials, then the
ring-to-scheme étale comparison. No step is omitted. All Lean lines are within 100
characters, and the node's `lean.statement` is verbatim the theorem signature.
