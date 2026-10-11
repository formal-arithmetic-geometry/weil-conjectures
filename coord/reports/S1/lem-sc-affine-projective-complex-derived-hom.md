## Worker report

The module states `CategoryTheory.affineProjectiveComplexDerivedHom` for complexes of
`ModuleCat R`. The hypotheses are a ring `R`, derived-category and Grothendieck-abelian
instances, complexes `P` and `L`, strict upper bound `d` on `P`, strict lower bound `e`
on `L`, and projectivity of every `P.X n`. The first conclusion
`P.IsKProjective` renders the bounded-above projective K-projectivity clause using
`CochainComplex.isKProjective_of_projective`; the second renders the boundedness estimate
as `IsZero ((HomComplex P L).homology n)` for every `n < e - d`.

Dependencies used are Mathlib `CochainComplex`, `CochainComplex.HomComplex`,
`CochainComplex.isKProjective_of_projective`, `CochainComplex.IsStrictlyLE`,
`CochainComplex.IsStrictlyGE`, `DerivedCategory`, and
`CochainComplex.kInjectiveResolutionFunctor` (the latter is documented in the proof
although the statement records its K-projective representative directly).

Edge cases checked: bounds are integer bounds and permit zero or empty terms; the
inequality is strict, so the threshold degree itself is not claimed to vanish; no
nonemptiness assumption on the index of the product is introduced. Searches used
`msearch.py leanfinder` for bounded-above projective derived Hom (no exact match),
`msearch.py loogle` for `CochainComplex.IsKProjective, DerivedCategory, HomComplex`
(no exact match), and `rg` over Mathlib and WeilConjectures (only the generic
K-projective and HomComplex declarations were found).

## Earlier second reading (a previous round; superseded)

Read the node and module independently. The ring, universe, derived-category,
Grothendieck-abelian, complex, strict-bound, and termwise-projective hypotheses all
appear explicitly. The conclusion has the K-projectivity clause and the explicit
negative-degree homology vanishing clause with the node's bound `n < e - d`.
The Lean uses Mathlib's HomComplex and K-projective notions rather than private copies.

## Second reading by S1

Read the node, all four statement-dependency nodes, their recorded source declarations,
and the delivered Lean independently. The earlier second-reading paragraph above is
superseded: it missed the absence of the representing isomorphism and the wrong codomain
of Mathlib's `HomComplex`.

Source reading: the local literature checkout contains lists but no Stacks tex files.
Read the official Stacks tex in sandbox scratchpad copies: cohomology.tex,
`lemma-stalk-internal-hom` (Tag 0GM8), its preceding
`lemma-pullback-internal-hom` proof (2), and conventions.tex, section Algebra.
Also read Tag 06XR on the official Stacks site. Tag 0GM8 compares with the singleton
ringed space at a stalk; its pseudo-coherence assumption belongs to that stalk comparison.
This node isolates the projective-complex computation used there, and does not claim
that arbitrary projective complexes are pseudo-coherent. Tag 06XR gives the
projective/injective-resolution calculation in the derived category.
The standing convention is commutative rings with identity and unitary modules,
including the zero ring. Thus `CommRing R` spells out the source's meaning of "ring";
it does not change the node. No node statement or dependency fields were changed.

Item-by-item matching of the node's objects, hypotheses and conclusions:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| A ring R, viewed as the structure ring of the one-point ringed site | `{R : Type u} [CommRing R]`, shared `CochainComplex.onePointRingSheaf R` | Correct under Stacks conventions; original `Ring` was too general for R-valued internal Hom. |
| R-modules on that site | `SheafOfModules.{u} ((sheafCompose ⊥ (forget₂ CommRingCat RingCat)).obj (onePointRingSheaf R))` | Correct: `Discrete PUnit.{u+1}` has a single object and only its identity; bottom topology imposes no further condition. A module presheaf is its value at that object, an R-module. This is the same encoding as landed `derivedHom_projectiveResolution`. |
| D(R), the localization at quasi-isomorphisms | `HasDerivedCategory.{w}` on this module category, and `DerivedCategory.Q` | Uses `def-weil-abstract-derived-category`; w is the chosen localization universe, not a finiteness assumption. |
| P and L are integer-indexed cochain complexes | `(P L : CochainComplex ... ℤ)` | Uses the recorded `CochainComplex`: objects, chain maps and d-square-zero agree with `def-pc-cochain-complex-modules`. |
| P is bounded above | `(d : ℤ) [P.IsStrictlyLE d]` | Its terms are zero for p>d, by the read Mathlib definition and `isStrictlyLE_iff`; any bounded-above P admits such a bound. |
| Every term of P is projective | `[∀ n : ℤ, Projective (P.X n)]` | Exactly the hypothesis in recorded `isKProjective_of_projective`; no finite generation or finite rank added. |
| L is bounded below | `(e : ℤ) [L.IsStrictlyGE e]` | Terms are zero for q<e by `isStrictlyGE_iff`; e is an arbitrary chosen bound. |
| Ordinary Hom with product degree-n terms | `CategoryTheory.homComplex (R := onePointRingSheaf R) P L` | Uses `def-pur-hom-complex` through the imported dependency. Read `homComplex_exists`, its product projections and differential, and the two selecting definitions. On this site its terms are precisely the R-module products in the node. |
| It represents derived internal Hom of P and L in D(R) | `Nonempty (Q.obj (homComplex ... P L) ≅ (derivedInternalHom ⊥ (onePointRingSheaf R)).obj (op (Q.obj P), Q.obj L))` | Restored missing main conclusion. Read `derivedInternalHom`, its localization lift and `derivedInternalHom_comparison`/`derivedInternalHom_obj_iso`: this is exactly the fixed K-injective-replacement construction of the recorded dependency. |
| Cohomology vanishes in all sufficiently negative degrees | `∃ a : ℤ, ∀ n : ℤ, n < a → IsZero ((homComplex ... P L).homology n)` | Exact existential conclusion of the node; the docstring supplies witness e-d from its proof. No extra cohomology vanishing at the threshold is claimed. |

The original `P.IsKProjective ∧ ...` omitted the representing isomorphism entirely.
K-projectivity is a proof step, not a replacement for that conclusion. Removed its
extra conjunct. The original uppercase `CochainComplex.HomComplex` is an abelian-group
complex: its module docstring and `Cochain` definition confirm this. Replaced it with
the shared lowercase sheaf-module-valued `CategoryTheory.homComplex` so the comparison
has the required codomain D(R). Removed the explicit Grothendieck-abelian assumption;
the shared derived-internal-Hom definition obtains it for small module sites. Replaced
an explicit cutoff conclusion by existential eventual vanishing, as the node says.
Added the standard header and expanded the proof docstring to the node's steps: resolve L,
use K-projectivity and the cone to get a quasi-isomorphism of Hom complexes, localize and
apply the shared comparison, then use the product degree estimate.

Edge cases: the zero ring and zero P or L are permitted (`CommRing`, with no
`Nontrivial`); their zero terms satisfy the projectivity and boundedness conditions.
All integer bounds and n=0 are permitted, including negative d/e. The proof cutoff
is strict, so it imposes no vanishing at e-d. The product indexes all integers and
allows factors to be zero; there is no nonemptiness or finiteness assumption on factors.
An empty scheme is irrelevant because this node has no scheme variable and concerns
the stated one-point site. Characteristic is unrestricted. The ring, modules and site
are allowed in arbitrary universe u; the one-point category is small in u, and
`homComplex`'s `max u u u` output reduces to u. The independent universe w only chooses
derived-category morphism sizes as in the recorded dependency. Every variable and
universe is explicitly bound; there is no file-local notation, instance or private copy.

Independent searches (different wording from the worker):

- `msearch.py leansearch "ordinary internal Hom complex from projective bounded above source represents derived internal Hom"`: service returned Internal Server Error; recorded unavailable, no mathematical verdict inferred.
- `msearch.py leanfinder "Hom complex of projective modules comparison with K injective replacement and lower cohomology vanishing"`: eight hits, including `isKProjective_of_projective`, `IsKProjective`, `ProjectiveResolution.extEquivCohomologyClass`, and `HomComplex.CohomologyClass.bijective_toSmallShiftedHom_of_isKProjective`. Opened the relevant K-projective source: these are ingredients or group-valued cohomology comparisons, not this internal-Hom object statement with bounded-below arbitrary L.
- `msearch.py grep "derivedInternalHom|homComplexFunctor|isKProjective_of_projective" Algebra/Homology`: only the K-projectivity lemma and its use in Mathlib.
- Independent `rg` in the project's Sheaf modules and upstream WeilConjectures for one-point/internal-Hom encodings and projective/bounded-below complex computations found the shared `onePointRingSheaf`, `homComplex`, `derivedInternalHom`, and landed `derivedHom_projectiveResolution`. Read all their signatures and defining data. The last lemma concerns resolutions of modules in degree zero, not arbitrary bounded-below target complexes; it does not realize this node. Strictly-perfect derived internal Hom concerns finite locally free bounded complexes, also a different hypothesis. No exact existing declaration or missing definition was found.

No new nodes or dependency modules are required: all notions are already shared.
Only this node's Lean record and its module were repaired. No definition was created;
the single theorem's proof remains `sorry`. The source and blueprint id occur in both
docstrings; the named dependencies and complete two-step mathematical argument are
included. `lcompile.py` compiled the repaired module cleanly (exit 0, 2.4 seconds).
