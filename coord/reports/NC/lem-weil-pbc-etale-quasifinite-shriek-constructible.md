## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible` states the main
quasi-finite assertion and its closed-immersion consequence. Both proofs are `sorry`.
There are no definitions, new nodes, dependency replacements, or statement corrections.
The source was read in `literature/stacks-project/more-etale.tex`, labels
`lemma-qf-f-shriek-constructible` (0GK3) and `lemma-Rf-shriek-for-quasi-finite` (0GKM).
The five proof steps of the node are recorded in the two theorem docstrings.

Hypothesis and clause correspondence:

- A finite commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  The universe follows the established six-functor coefficient encoding.
- Schemes are `{T B : Scheme.{u}}`; each has `[CompactSpace _]` and
  `[QuasiSeparatedSpace _]`, exactly the qcqs assumptions.
- The named morphism is `(h : T ⟶ B)`.
- Separatedness is `[IsSeparated h]`; finite type is `[LocallyOfFiniteType h]`
  and `[QuasiCompact h]`.
- Quasi-finiteness is `(hqf : h.IsQuasiFinite)`, the dependency's Stacks predicate,
  including finite type and isolation of every fibre point. No substitution of the weaker
  Mathlib `LocallyQuasiFinite` predicate is made.
- Finite presentation is `[LocallyOfFinitePresentation h] [QuasiCompact h]
  [QuasiSeparated h]`, as fixed by the scheme-conventions node. Some finite-type and
  compactness hypotheses overlap logically; they express explicitly the node's clauses.
- `K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`
  is exactly the bounded-below derived category of module sheaves on the small etale site.
- `hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
  ((DerivedCategory.Plus.homologyFunctor _ q).obj K)` is constructible cohomology
  in every degree. The constructibility predicate is precisely the dependency's finite
  stratification with constructible parts and finite locally constant module restrictions.
- `(c : Compactification h)` includes the intermediate scheme, open immersion `c.i`,
  proper map `c.g`, and factorization equality. `[QuasiCompact c.i]` supplies the exact
  additional requirement of the node (the upstream structure itself does not impose it).
  Since `c` is a binder, the conclusion holds for every such compactification.
- `rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c` is the
  existing bounded-below functor `D+(c.i_!) ⋙ R+(c.g_*)`. The conclusion applies
  `DerivedCategory.Plus.homologyFunctor` in every integer degree to its value at `K`,
  and asserts the same constructibility predicate on B.
- `constructibleCohomology_lowerShriek_of_isClosedImmersion` states the final
  “in particular” clause explicitly: replace the morphism assumptions by
  `[IsClosedImmersion h] [LocallyOfFinitePresentation h]`; closed immersion already
  implies quasi-compact and separated, hence quasi-separated. It keeps the qcqs schemes,
  coefficient ring, K, constructible-cohomology hypothesis, and arbitrary compactification.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `def-weil-pbc-scheme-conventions` is convention-only, with no module/declaration;
  its named Mathlib properties are used directly.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` and its
  `rightDerivedLowerShriekOfCompactificationPlus` counterpart. Its definition uses
  `WeilConjectures.Compactification.Defs`, `AlgebraicGeometry.Compactification`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`, used through that composite.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, whose `Functor.rightDerivedFunctorPlus` is
  the pushforward factor of the composite (the current source uses the generic derived
  functor rather than the older recorded `rightDerivedLowerStarPlus` name).
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the documented
  `AlgebraicGeometry.Etale.DerivedCategoryModule` encoding, `DerivedCategory.Plus`,
  and homology functors. No torsion predicate is needed since the coefficients are finite.
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFinite`.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.

The stated proof dependencies with modules have private imports: OpenClosed.Complex,
OpenImmersion.FiniteComparison, UpperLowerStar.Stalk, SixFunctors.Finite.Exact,
Mathlib AlgebraicGeometry.Sites.EtalePoint and Morphisms.Finite. The constructible-subset
predicate and other definitional/proof material are already available through the public
statement imports. The factorization, finite-fp pushforward constructibility, and
compactification-independence nodes currently have no Lean records, so have no module to
import; their future statements are named in the proof plan rather than invented here.

Edge cases checked: the empty source and target are not excluded; zero module sheaves
and the zero coefficient ring are allowed; q ranges over all integers, including negative
ones; K is only bounded below, with no uniform upper bound, finite Tor amplitude,
Noetherian base, characteristic restriction, or nonempty-scheme assumption. Arbitrary
compactifications are permitted, not only the finite factorization used in the proof.
Finite presentation is essential to constructible pushforward over a non-Noetherian base.
No STATEMENT-DISPUTED issue was found.

Searches (no matching existing theorem):

- `msearch.py leanfinder`, query `Quasi finite finitely presented morphism shriek preserves
  constructible cohomology on etale sites`: eight hits, concerning images of constructible
  subsets, quasi-finite ring maps and quasi-coherent finite presentation. Read the returned
  types/docstrings: none concerns constructible module-sheaf cohomology or lower shriek.
- `msearch.py loogle`, query `"shriek", "constructible"`: zero hits.
- `msearch.py grep`, query `shriek|constructible.*cohomology`: zero hits in Mathlib.
- `msearch.py leansearch`, query `Quasi finite etale lower shriek preserves constructible
  cohomology`: service unavailable (Internal Server Error); no verdict inferred.
- `rg` of upstream WeilConjectures and this project's lean/Sheaf for
  `quasifinite.*[Cc]onstruct|quasiFinite.*[Cc]onstruct` and the item id: no hits.
  Broader constructible-cohomology search found bounded constructible categories and
  pro-etale definitions, not this bounded-below assertion.
- `rg` of `dag/lean_names_upstream.json`, upstream and lean/Sheaf for the proposed theorem
  names: no hits; no declaration-name collision.

Validation: `scompile.py NC lem-weil-pbc-etale-quasifinite-shriek-constructible` on the
module passed cleanly on the server in 1.6 seconds (nice 19, two threads, 60-second limit).


## Second reading by NC

Independently read the node, both theorem signatures and docstrings, all nine statement
dependency records, and the declaration bodies/signatures they use. Read More on Etale
Cohomology at `lemma-qf-f-shriek-constructible` (0GK3), including its section convention
that the coefficient ring is Noetherian, and `lemma-Rf-shriek-for-quasi-finite` (0GKM).
A finite commutative ring is Noetherian and torsion, so this specialization requires no
additional ring hypothesis. The separated qcqs case and bounded-below restriction are
exactly the node's chosen specialization of those sources.

Object, hypothesis and conclusion checklist (all pass):

1. Finite commutative ring Λ: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` in both
   statements. This is the established coefficient universe of the dependency, not a
   restriction to fields, nonzero rings, or invertible characteristic.
2. Schemes T and B: `{T B : Scheme.{u}}`, with `CompactSpace` and
   `QuasiSeparatedSpace` on each, render precisely qcqs schemes.
3. Named scheme morphism h: `(h : T ⟶ B)`. Its separatedness is `[IsSeparated h]`;
   finite type is `[LocallyOfFiniteType h] [QuasiCompact h]`.
4. Quasi-finiteness: `(hqf : h.IsQuasiFinite)`, using the recorded
   `Scheme.Hom.IsQuasiFinite` from `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`.
   Opened its definition: finite type plus openness of each singleton in its
   scheme-theoretic fibre, exactly the node's isolated-fibre-point condition.
   The repeated finite-type instances add no mathematical requirement.
5. Finite presentation: `[LocallyOfFinitePresentation h] [QuasiCompact h]
   [QuasiSeparated h]`, in the sense explicitly fixed by the conventions node.
   Read the Mathlib local-finite-presentation class. Quasi-separatedness is also
   implied by separatedness; no stronger hypothesis is introduced.
6. K: `DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
   Opened `DerivedCategories`, the source's `DerivedCategoryModule` abbreviation,
   and `DerivedCategory.Plus.homologyFunctor`: the latter is inclusion into the
   derived category followed by its homology functor. This is D+ and H^q of the
   dependency, without boundedness above or finite Tor amplitude.
7. Constructible cohomology of K: `hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
   ((DerivedCategory.Plus.homologyFunctor _ q).obj K)`. Opened the predicate:
   finite locally closed stratification, constructible parts, etale trivializations,
   and finite constant module values, exactly the recorded constructibility node.
8. Compactification: `(c : Compactification h) [QuasiCompact c.i]`. Opened the source
   structure: ambient scheme Z, open immersion i, proper g, and h = i ≫ g.
   The separate quasi-compactness instance is necessary to render the node because
   the upstream structure does not include it. c is arbitrary, not chosen once.
9. Rh_!^c: `rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c`.
   Opened its body: exact derived open extension by zero followed by bounded-below
   right derived direct image. Also read `openImmersionLowerShriek` and `lowerStar`,
   the latter defined by the etale base-change sheaf pushforward. This is Rp_*j_!.
10. Conclusion: `∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf` of the homology
    of that functor applied to K, on B. All degrees and every compactification are
    quantified; the placement of c after K is equivalent to the node's universal
    quantifiers because neither K nor its hypothesis depends on c.
11. In particular, a closed immersion of finite presentation: the second theorem
    retains Λ, qcqs T and B, K, hK, c, and its quasi-compact open immersion, and uses
    `[IsClosedImmersion h] [LocallyOfFinitePresentation h]`. Closed immersions are
    finite, separated and quasi-compact, and have empty or singleton fibres; these
    hypotheses give exactly the stated consequence, including quasi-separatedness.

Edge cases: empty T and empty B are allowed (no Nonempty binder); zero ring and zero
sheaf/complex are allowed; q ranges over every integer, including zero and negatives;
there is no n > 0 condition and the stratification definition allows n = 0. Finite
coefficient characteristic is unrestricted, including characteristic dividing residue
characteristics. The common scheme universe and successor module/coefficient universe
are the recorded six-functor encoding, with no independent smaller test-object universe.
There is no Noetherian scheme assumption or implicit finite-dimensional hypothesis.

Independent H4 searches: `msearch.py loogle '"constructible", "lowerShriek"' returned
zero hits; `msearch.py leanfinder 'Exceptional direct image of a finitely presented
quasi finite map preserves constructible etale module sheaves'` returned eight results.
Read their types: scheme/spectrum constructible-image theorems and etale-locus results,
not a constructible-cohomology statement. `msearch.py leansearch 'Exceptional image
quasi finite constructible module sheaf cohomology'` was unavailable (Internal Server
Error); no negative verdict is inferred. Independently ran `rg` in Mathlib, upstream
WeilConjectures, and project lean/Sheaf for constructibility with shriek/exceptional in
both orders and for both proposed theorem names. Opened the closest upstream results:
`boundedConstructible_rightDerivedLowerShriek` assumes schemes locally of finite type
over a field, invertible exponent, and bounded input; the finite-Tor stability theorem
adds Tor hypotheses, and open-immersion results address only open immersions. None is
this arbitrary-qcqs, all-characteristics, merely bounded-below quasi-finite assertion.
The proposed declaration names have no collision in project/upstream sources or the
upstream name inventory.

No mismatch found; retained both statements and their docstrings unchanged. There are
no new nodes, dependency modules, statement corrections, hollow definitions, private
notions, file-local notation, or added proofs. The two sorry proofs are named theorems,
and their source-labelled docstrings cover all five proof steps (steps 1–4 in the main
statement and step 5 in the consequence). Checked imports against the stated notions
and recorded proof dependencies. Verified `lean.statement` is verbatim the first theorem
signature; all variables and the sole universe u are explicitly bound.
