## Worker report

The module `Sheaf.RingTheory.EtaleColimitNormalLocalDomain` states
`CommAlgCat.isDomain_isIntegrallyClosed_injective_of_etale_colimit`, with a single
`sorry` proof and the complete six-step DAG proof in its docstring. No definitions,
new nodes, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:

- A is a commutative integral domain: `(A : Type u) [CommRing A] [IsDomain A]`.
- A is normal in the node's prime-local sense: `hA : ∀ (p : Ideal A)
  [p.IsPrime], IsDomain (Localization.AtPrime p) ∧
  IsIntegrallyClosed (Localization.AtPrime p)`. This is precisely the inline
  conjunction supplied by `def-weil-pbc-normal-ring.mathlib_match`, not a new notion.
- I is a filtered indexing category: `{I : Type w} [Category.{w'} I]
  [IsFiltered I]`. The last class includes nonemptiness, common successors,
  and equalization of parallel arrows. Both universes are explicit.
- The diagram consists of commutative A-algebras and A-algebra transition maps:
  `B : I ⥤ CommAlgCat.{v} A`. The algebra-carrier universe v is independent of
  the universe u of A and the indexing universes.
- C is the colimit of this diagram: `c : Cocone B` and `hc : IsColimit c`;
  C is `c.pt`. The cocone provides the compatible coprojections and `hc`
  their universal property. This quantifies over any given colimit C, rather
  than imposing a particular chosen representative or an equality of types.
- Each Spec(B_i) → Spec(A) is etale: `hB : ∀ i : I, Algebra.Etale A
  (B.obj i)`. This uses the ring-algebra encoding expressly allowed by
  brief-stage2 §3, ÉTALE RING MAPS. `RingHom.etale_algebraMap` identifies
  it with etaleness of the structure ring map, and the
  `HasRingHomProperty @AlgebraicGeometry.Etale RingHom.Etale` bridge identifies
  it with the recorded scheme property on Spec. No extra hypothesis is imposed.
- C is local: `[IsLocalRing c.pt]`. This class includes nontriviality, as the
  source's convention for local rings requires.
- Conclusion (a), C is a normal domain: `IsDomain c.pt ∧
  IsIntegrallyClosed c.pt`. The latter is integral closedness in `FractionRing c.pt`,
  exactly the normal-domain part of the recorded dependency conjunction.
- Conclusion (b), A → C is injective: `Function.Injective (algebraMap A c.pt)`.
  For ring homomorphisms this is equivalent to every nonzero element having
  nonzero image, including the clause as written in the node.
- The strict-henselization parenthesis is an application of these hypotheses,
  not a further hypothesis or conclusion; it introduces no additional binder.

Dependencies read and used:

1. `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone` and
   `CategoryTheory.Limits.IsColimit` (Mathlib.CategoryTheory.Limits.Cones and
   Mathlib.CategoryTheory.Limits.IsLimit, available through CommAlgCat.Basic),
   and `CategoryTheory.IsFiltered` (Mathlib.CategoryTheory.Filtered.Basic).
   Read the recorded chosen `colimit` interface in Limits.HasLimits and the
   full cocone and IsColimit structures; the arbitrary cocone presentation
   gives the same universal property for the specified C.
2. `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`
   (Mathlib.AlgebraicGeometry.Morphisms.Etale), represented here by its equivalent
   `Algebra.Etale` (Mathlib.RingTheory.Etale.Basic), per the explicit convention.
   Read both class declarations and RingHom.etale_algebraMap in
   Mathlib.RingTheory.RingHom.Etale.
3. `def-weil-pbc-normal-ring`: its mathlib_match explicitly supplies
   `IsDomain`, `IsIntegrallyClosed` (Mathlib.RingTheory.IntegralClosure.IntegrallyClosed),
   and `Localization.AtPrime` (Mathlib.RingTheory.Localization.AtPrime.Basic),
   used as the indicated one-line conjunctions. It has status mathlib and no
   lean record is necessary or changed.

Edge cases checked: empty I is excluded by filteredness itself, not an extra
condition; a zero C is excluded by the local-ring convention; zero individual
B_i are permitted, so no domain or injectivity assumption is imposed on stages;
transition maps need not be injective; A can be a field; no Noetherian, local-A,
characteristic, countability, poset, or finiteness hypothesis is added. All
variables and universes are explicitly bound. Normal-domain integral closedness
is a conjunction with IsDomain, so no erroneous fraction-field interpretation
for zero rings is used in the conclusion. No statement fault or dispute found.

Source check: the local Stacks checkout is absent on this machine. Read the
primary online sources [06DI](https://stacks.math.columbia.edu/tag/06DI),
[033C](https://stacks.math.columbia.edu/tag/033C), and
[037D](https://stacks.math.columbia.edu/tag/037D). These support the ascent,
filtered-colimit, and local-normal arguments. The injectivity argument is the
node's additional six-step argument, retained in full in the Lean docstring.

Searches (msearch.py with group K1 and this item; 2026-10-11):

- leansearch: `local filtered colimit of etale algebras over a normal domain is
  an integrally closed domain`: UNAVAILABLE, Internal Server Error. No match claimed.
- leanfinder: `A local filtered colimit of etale algebras over a normal domain is
  an integrally closed domain and the structure map is injective`: eight hits,
  including Algebra.Etale.exists_subalgebra_fg, Algebra.exists_etale_of_isEtaleAt,
  RingHom.Etale.ofLocalizationSpanTarget/ofLocalizationSpan, Algebra.IsEtaleAt,
  Algebra.IsEtaleAt.comp, and Algebra.Etale.of_isLocalization_Away/of_isLocalizationAway;
  none states normality of a local filtered colimit or both required conclusions.
- loogle: `Algebra.Etale, IsIntegrallyClosed`: zero hits.
- grep Mathlib/RingTheory:
  `([Ee]tale.*(colimit|[Ii]ntegrallyClosed)|([Ii]ntegrallyClosed|[Nn]ormal).*(colimit|[Ee]tale))`:
  zero hits.
- rg over source WeilConjectures and project's lean/Sheaf:
  `etale.*(colimit|normal)|normal.*(colimit|etale)|EtaleColimit|etale_colimit|lem-weil-pbc-etale-colimit-normal-local-domain`:
  related scheme normal-component, generic-constant, and etale descent modules,
  but no statement of this node. The exact item ID has no source match.
- Checked the new declaration's full short name in dag/lean_names_upstream.json,
  WeilConjectures and lean/Sheaf: no collision.

Validation: scompile.py compiled the 60-line module on the server in 1.5 seconds,
exit code 0, with no warnings. The final delivery dry run follows; the independent
second-reading section is intentionally reserved for the second reader.

## Second reading by K1

I independently opened the item node, its delivered module and node copy, all
three statement-dependency nodes, and the Mathlib declarations behind their
records. No mathematical mismatch was found. The Lean module is unchanged.
The only repair is to `lean.statement`: the worker recorded a whitespace-flattened
signature; I restored the literal multiline signature from the theorem keyword
to immediately before `:=`, as the second-reader brief requires.

Object, hypothesis and conclusion checklist (all verdicts: exact):

1. Commutative integral domain A: `(A : Type u) [CommRing A] [IsDomain A]`.
   The domain includes nontriviality; A is not assumed local or a field.
2. Normality of A at every prime: `hA : ∀ (p : Ideal A) [p.IsPrime],
   IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
   This is exactly the conjunction accepted in def-weil-pbc-normal-ring's
   mathlib_match, rather than an independently invented normal-ring predicate.
   I read `Localization.AtPrime = Localization p.primeCompl` and
   `IsIntegrallyClosed R = IsIntegrallyClosedIn R (FractionRing R)`; the
   elementwise `isIntegrallyClosed_iff` confirms integral closedness in Frac(R).
3. Filtered indexing category I: `{I : Type w} [Category.{w'} I] [IsFiltered I]`.
   I read IsFilteredOrEmpty's two cocone fields and IsFiltered's Nonempty field.
   They give all three clauses in def-weil-pbc-category-colimit, including
   equalization of parallel arrows; I is not restricted to a directed poset.
4. Diagram of A-algebras and A-algebra transition maps:
   `(B : I ⥤ CommAlgCat.{v} A)`. I read CommAlgCat's carrier, CommRing and Algebra
   fields and its morphism structure `A →ₐ[R] B`. Its maps preserve the specified
   A-structure; they are not required to be injective, local, or etale.
5. Spec(B_i) → Spec(A) etale for each object:
   `hB : ∀ i : I, Algebra.Etale A (B.obj i)`.
   I read Algebra.Etale, RingHom.Etale, `RingHom.etale_algebraMap`, the scheme
   Etale class and `HasRingHomProperty @Etale RingHom.Etale`. These identify
   the algebra predicate with the dependency's affine scheme predicate. The
   explicit ETАLE RING MAPS convention allows this encoding. Finite presentation
   of each structure map belongs to etaleness, not an added finiteness assumption.
6. Specified colimit A-algebra C: `(c : Cocone B) (hc : IsColimit c)`, with C
   represented by `c.pt`. I read Cocone's natural transformation and IsColimit's
   desc/fac/uniq fields, as well as the recorded chosen colimit interface.
   These give the same universal property and compatible A-algebra coprojections
   for arbitrary C, without a restriction to a chosen representative.
7. Locality of C: `[IsLocalRing c.pt]`. I read the class, which extends
   Nontrivial and supplies the usual local-ring condition for a commutative ring.
   This agrees with the source's proper maximal-ideal convention.
8. Conclusion (a): `IsDomain c.pt ∧ IsIntegrallyClosed c.pt`, precisely a
   normal domain, including both domain and integral-closedness clauses.
9. Conclusion (b): `Function.Injective (algebraMap A c.pt)`, equivalent for a
   ring homomorphism to nonzero elements having nonzero images. This is the
   structure map of the same cocone vertex, not an arbitrary map.
10. The strict-henselization parenthesis is the stated application of these
    hypotheses, not a further quantified object or a separate conclusion.
    The theorem's quantifier order matches the node's data and hypotheses.

Source reading: literature/stacks-project is not present in this clone. I read
both the primary Stacks tag pages and the actual source TeX from
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex
(label lemma-henselization-normal), and algebra.tex (labels
lemma-normal-goes-up, lemma-colimit-normal-ring, definition-domain-normal,
definition-ring-normal). Tag 06DI's local base is for its henselization application;
the colimit argument uses only normality of the base and locality of the result.
Tag 033C explicitly includes the non-Noetherian case. Tags 0309 and 00GV give
exactly the two meanings of normality used here. Tag 037D imposes no injectivity
condition on transitions. The node's extra conclusion (b) follows by its written
flatness/nonzero-colimit argument; it is not claimed to be a separate assertion
of 06DI. No omitted ambient hypothesis or statement correction was found.

Edge cases: an empty I is excluded by the source's filteredness and by IsFiltered;
zero A is excluded by IsDomain; zero C by IsLocalRing. A zero B_i (empty affine
scheme) is allowed: no domain or nontriviality instance is required for B_i.
The proof docstring correctly derives a contradiction only after such a stage
maps unitally to C. Fields A, positive and zero characteristic, non-Noetherian
bases, noninjective transition maps and arbitrary filtered categories are all
covered. There is no n parameter. The four explicitly declared universes
`u v w w'` independently allow the base, algebra carriers, objects and arrows;
there is no unintended universe equality or unbound variable.

Independent searches, with different wording from the first reader (2026-10-11):

- LeanFinder via msearch.py: "a local inductive limit of smooth commutative
  algebras over a normal integral domain is integrally closed and the base embeds".
  Eight hits: local-to-global integral-closedness lemmas, localization of integral
  closure, ZariskisMainProperty, IsSmoothAt and almost-integral closure. None
  states this colimit theorem or both conclusions.
- Loogle via msearch.py: `IsIntegrallyClosed, CommAlgCat`: zero hits.
- LeanSearch via msearch.py: "filtered direct limit of étale algebras over a
  normal domain is a normal domain when the limit is local": unavailable with
  Internal Server Error. No match or absence verdict is claimed from that service.
- rg over Mathlib/RingTheory, source WeilConjectures and project lean/Sheaf:
  `(integrallyclosed|normal.?ring|normal.?domain)` paired in either order with
  `(directlimit|inductive|filtered|etale|smooth)`, case-insensitively. The hits
  concern normal scheme components, smooth stalks and constant-sheaf results,
  not this theorem. Exact-name and alternative NormalRing/IsNormalRing and
  Etale/DirectLimit searches over all Mathlib, source, project and
  dag/lean_names_upstream.json found no duplicate declaration or shared predicate.

H5/H6/H8/H9: no definitions or private copies, exactly one named theorem with
`sorry`, no proved helper, correct namespace and topic, every line at most 100
characters. Both docstrings name the source and blueprint item; the statement
retains all six proof steps and their dependencies. There are no new definition
nodes, dependency modules, or statement corrections to audit under H12/H13.

Validation: scompile.py on the absolute sandbox module path returned exit code 0,
compiled in 1.5 seconds, with no warnings. The original relative-path invocation
could not find the sandbox module from the read-only repository cwd; using the
absolute path resolved that invocation error. The node record now equals the
literal signature; all other node fields and the module remain unchanged.
