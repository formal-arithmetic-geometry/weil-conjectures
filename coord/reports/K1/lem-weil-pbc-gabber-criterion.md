## Worker report

The module states `AlgebraicGeometry.Etale.gabberCriterion`. The ring hypothesis is rendered by `R : Type u`, `[CommRing R]`, and `∀ p [p.IsPrime], IsStrictlyHenselianLocalRing (Localization.AtPrime p)`. The sheaf is `F : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u+1}`. Principal opens are Mathlib's `PrimeSpectrum.basicOpen`; their inclusion and restriction are `Scheme.Opens.ι` and the inverse image functor. The degree-one assumption is expressed as: if both restriction maps, implemented by `AlgebraicGeometry.Etale.cohomologyMap` along `Scheme.homOfLE`, send a class to zero, then the class is zero. The conclusion is `∀ q, 0 < q → Subsingleton (Sheaf.H F q)`.

Dependencies used: `Sheaf.RingTheory.HenselianTerminology.IsStrictlyHenselianLocalRing`; Mathlib `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Scheme.smallEtaleTopology`, `AlgebraicGeometry.IsOpenImmersion`; upstream `AlgebraicGeometry.Etale.cohomologyMap` and `AlgebraicGeometry.Etale.cohomology` records were consulted. The proof is `sorry` as required.

Edge cases checked: `h = 0` and `f+g = 0` are represented by Mathlib basic opens without exclusions; `q = 0` is excluded exactly by `0 < q`; arbitrary universe `u` is retained.

Searches: `msearch.py leanfinder` for Gabber/strict henselian étale cohomology (no match); `msearch.py loogle` and grep of Mathlib/source for Gabber criterion (no match); `rg` of project source found no existing criterion declaration. Existing `cohomologyMap` and `IsStrictlyHenselianLocalRing` were reused.

## Earlier second reading (a previous round; superseded)

Read the node and module. The ring, strict henselian local, affine spectrum, étale sheaf, principal-open restriction, injectivity hypothesis, and positive-degree subsingleton conclusion correspond clause by clause. No hypotheses or conclusion clauses were added or dropped.

## Second reading by K1

Read the sandbox node, its complete five-step proof, GabberCriterion.lean, and
all eight statement-dependency nodes and their recorded declarations. Read the
Stacks source `etale-cohomology.tex`, lines 14196–14295, in the available local
Stacks source copy: the section's introductory paragraph, Lemma 09AX, and
Lemma 0GY0 (`lemma-gabber-criterion`) and its proof. The repository's recorded
literature path is absent on this machine; the local source copy contains the
exact labels and text at the recorded lines. There are no additional standing
Noetherian, finiteness, torsion, characteristic, or local-ring assumptions.

Clause-by-clause list (objects, hypotheses, conclusion):

1. A commutative ring R: `(R : Type u) [CommRing R]`. Matches; no field,
   nontriviality, Noetherian, or finiteness assumption is added.
2. Every prime localization R_p is strictly henselian: `hR : ∀ (p : Ideal R)
   [p.IsPrime], IsStrictlyHenselianLocalRing (Localization.AtPrime p)`.
   Matches every prime, not merely maximal primes. Read
   HenselianTerminology.lean: the recorded predicate is exactly
   `HenselianLocalRing A ∧ IsSepClosed (IsLocalRing.ResidueField A)`;
   the local-ring instance on the prime localization is automatic. No
   extra hypothesis on R being local is present.
3. S = Spec R: `Spec (CommRingCat.of R)`. Matches the spectrum dependency's
   `AlgebraicGeometry.Spec` definition in Mathlib Scheme.lean:470.
4. An arbitrary abelian sheaf F on the small etale site of S:
   `F : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology
   AddCommGrpCat.{u + 1}`. Matches. Read Mathlib Sites/Etale.lean:51 and
   Sites/Sheaf.lean:302: this is the topology on etale S-schemes and the
   full subcategory of presheaves satisfying its sheaf condition.
5. Principal open D(h), its immersion j_h, and restricted sheaf:
   `PrimeSpectrum.basicOpen h`, `Scheme.Opens.ι`, and
   `((j_h)^*[AddCommGrpCat.{u + 1}]).obj F`. Matches. Read
   Restrict.lean:46–57: the open coerces to its restricted scheme and its
   inclusion is an open immersion. Read upstream UpperLowerStar/Defs.lean:
   `upperStar` is sheafified inverse image, with the recorded adjunction.
   No private definition or extra open-immersion hypothesis is needed.
6. Restriction for D(h') contained in D(h): `cohomologyMap` along
   `Scheme.homOfLE`. Matches the pullback dependency. Read
   Restrict.lean:241–247 and TopologicalInvariance.lean:174–188: the
   morphism composes with j_h to j_h', and the additive cohomology map
   has target H of the inverse-image sheaf. Here that target is an
   iterated inverse image; the canonical composition isomorphism identifies
   it with j_h' inverse image of F. Its induced additive isomorphism
   preserves zero, so testing the displayed map for zero is equivalent
   to the node's test after the canonical identification.
7. For every f,g the degree-one pair of restrictions has zero kernel:
   `hfg : ∀ (f g : R) (x : Sheaf.H ... 1), ... = 0 → ... = 0 → x = 0`.
   The source is exactly D(f+g), and the targets exactly D(f(f+g)) and
   D(g(f+g)). Their inclusions now use the existing
   `PrimeSpectrum.basicOpen_mul_le_right f (f + g)` and its g analogue.
   The two simultaneous zero tests are precisely zero kernel of the map
   to the two-term direct sum; no surjectivity or vanishing of H^1 is
   assumed. The quantifier order matches: fix R and F, then all f,g,x.
8. All positive-degree etale cohomology on S vanishes:
   `∀ (q : ℕ), 0 < q → Subsingleton (Sheaf.H F q)`. Matches: this
   additive cohomology type is subsingleton precisely when every class
   is zero. Read Mathlib SheafCohomology/Basic.lean:59 and upstream
   Derived/LowerShriek.lean:235. As the cohomology and pullback dependency
   records explicitly permit, this uses the shared Ext form `Sheaf.H`
   and its `cohomologyMap`; its comparison with the recorded derived
   global-sections form is the existing stage-3 bridge obligation.
   No second cohomology definition or unusable dependency module is needed.

Edge cases: the zero ring and its empty spectrum are permitted because only
CommRing is required and the prime condition is then vacuous. Empty principal
opens (h=0, f+g=0, f=0 or g=0, nilpotents) are not excluded. The zero sheaf
is permitted. There is no indexed-family nonemptiness assumption. q=0 is
excluded exactly by 0<q, as in the source; all positive natural degrees occur.
There is no characteristic restriction. The universe u is declared and
arbitrary; the coefficient universe u+1 is the recorded small-etale-site
encoding, allowing any such ring/sheaf pair after raising u if necessary.
There are no implicit additional assumptions or unbound variables/universes.

Independent searches (different wording from the worker):

- LeanFinder through msearch: “positive degree sheaf cohomology vanishing
  affine scheme strictly henselian localizations Gabber”. Eight unrelated
  results concerning affine limit sections and derived projective/injective
  vanishing; no criterion declaration.
- Loogle through msearch: `"gabber"`. Zero results.
- LeanSearch through msearch: “vanishing of higher etale cohomology on
  principal open subsets from degree one injectivity”. Service unavailable
  (Internal Server Error), recorded without a mathematical verdict.
- rg of Mathlib sheaf-cohomology and henselian source, all upstream
  WeilConjectures, and project lean/Sheaf using “Gabber”, “Mayer-Vietoris”,
  “strictly henselian”, and exact criterion/tag spellings. Opened the
  relevant shared definitions above. The upstream Gabber module states
  henselian-pair comparison and effacement, not this criterion; the project
  strictly-henselian acyclicity statement assumes a local ring, not all
  prime localizations with this kernel hypothesis. No exact existing
  statement; no new nodes or dependency modules are delivered.

Mismatches and repairs: no mathematical mismatch and no node-statement
correction. Removed both inline `show ... by` proofs from the statement,
replacing them by Mathlib's existing basic-open inclusion theorem (the
brief forbids hidden-have expressions in statements). Added the missing
copyright header and module source docstring. Expanded the theorem's
one-sentence proof sketch into the complete five-step node proof, including
the simultaneous induction, I_h, the hf/hg degree-one application,
Mayer-Vietoris intersection, radical argument, and conclusion at h=1.
Documented the canonical identification of the target sheaves. Replaced the
unused Away.Basic import with the directly used AtPrime.Basic, and removed
the unused Limits opening. Kept the mathematical statement unchanged and
updated lean.statement verbatim to the repaired signature. There are no
hollow definitions, extra proved declarations, private notions, file-local
notation, or local instances; the sole theorem proof remains `sorry`.

Validation: scompile compiled the repaired single module in 4.6 seconds,
exit code 0, with no warnings. All lines have at most 100 characters.
