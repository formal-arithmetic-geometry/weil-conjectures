## Worker report

The delivery states `CategoryTheory.sliceAwayLocalization_free_resolution` in
`Sheaf.CategoryTheory.SliceAwayLocalizationFreeResolution`. Its only proof is `sorry`.
The auxiliary module defines `CategoryTheory.SliceAwayLocalization` as actual presheaf
data with coherent linear coordinates; it has no sorry and makes no choice from an
unproved existence theorem. The main theorem includes existence of this presheaf model,
so it does not assume an unspecified localization exists.

Source read: `literature/stacks-project/algebraization.tex`, Tag 0997,
`lemma-hom-from-Af`, lines 833–874, especially the displayed resolution and its two
formulas. Also read `sites-modules.tex`, `definition-ringed-site`, and
`conventions.tex` line 51: Stacks rings are commutative with 1. Thus `CommRingCat`
expresses the source convention, rather than adding a mathematical hypothesis.
No change to the item's natural statement was needed.

Hypotheses and clauses, individually:

- The site is `{C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}`;
  both category universes are explicitly bound.
- The ring sheaf is `O : Sheaf J CommRingCat.{u}`. The standard forgetful functor
  `sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})` supplies the ring-valued
  sheaf for Mathlib's module API. `J.HasSheafCompose` explicitly supplies the
  universe-dependent infrastructure for that functor. It does not constrain O or f.
- The object is `(U : C)`, and its section is `(f : O.obj.obj (op U))`.
- The localized site is `J.over U`, with underlying category `Over U`; the
  restricted ring sheaf is the existing `Sheaf.over` of the ring-valued O.
- `HasSheafify (J.over U) AddCommGrpCat.{u}` and
  `(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}` are exactly the existing
  module-sheafification and abelian-category API requirements of the dependency
  records. They make the source's implicit sheafification infrastructure explicit;
  no geometric, Noetherian, nonzero, or regularity assumption is imposed. Object,
  hom and ring universes remain independent, subject to these infrastructure instances.
- `∃ L : SliceAwayLocalization O U f` supplies the presheaf whose sections are
  O(V)[1/f|V], with linear isomorphisms `L.equiv V` and the precise restriction rule.
  Its coordinates exhaust the localizations, so this is a presentation of the
  specified presheaf, not a different target object. Any two such presentations
  have the unique coordinate-preserving natural isomorphism; transporting the
  resolution along its sheafification gives the statement for either presentation.
- The third object is exactly
  `(PresheafOfModules.sheafification (𝟙 restrictedRing.obj)).obj L.val`, i.e. the
  dependency's module sheafification, including its linear structure.
- Both free objects are `SheafOfModules.free (R := restrictedRing) (ULift.{u} ℕ)`.
  This is Mathlib's coproduct of copies of the unit module, not a sectionwise
  direct sum. `ULift` only moves the countable indexing set into the ring universe.
- The maps are existentially bound sheaf morphisms `d` and `q`. Their coordinate
  formulas determine them uniquely since the source is that coproduct.
- `∃ h : d ≫ q = 0, (ShortComplex.mk d q h).ShortExact` renders the complete
  sequence, including injectivity at the first nonzero term, exactness in the
  middle, and surjectivity at the last nonzero term. The short-complex category is
  explicitly the dependency `ringedSiteModules restrictedRing`.
- The d formula says, for every slice object V, coordinate n, and scalar a,
  `d(ι_n(a)) = ι_n(a) - ι_(n+1)((f|V)*a)`. Summing gives precisely zeroth coordinate
  x0 and later coordinates x_n - f*x_(n-1), including the last shifted coordinate.
- The q formula says `q(ι_n(a))` is the image of a/f^n under the component of the
  sheafification-adjunction unit on L. The fraction is written
  `algebraMap _ _ a * IsLocalization.Away.invSelf (f|V) ^ n` and placed in L through
  `(L.equiv V).symm`. Finite sums yield the node's displayed q formula. Sections
  of the sheaf coproduct are only locally such sums; no global finite-support
  restriction has been added.

Dependencies read and used:

- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules` (full module read). This abbreviation is used
  explicitly as the category of the short complex, with inherited Mathlib structures.
- `def-pur-localized-ringed-site`: Mathlib leaf, `Mathlib.CategoryTheory.Sites.Over`,
  `J.over`, `Sheaf.over` (declaration/docstring read at line 512); and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.over`, `overFunctor`, `Hom.over`, `overMap`, `overFunctorMap`
  (full signatures/docstrings read at lines 59–85). Only the slice/ring restriction
  is needed for this statement; the module restriction API is publicly imported.
- `def-weil-presheaf-modules-sheafification`:
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
  `PresheafOfModules.sheafification (𝟙 _)` and `sheafificationAdjunction` (read
  lines 30–192). The latter's unit gives the map from fractions to the associated sheaf.
- The proof dependency `lem-weil-pbc-ringed-site-module-sheafification-exact` is a
  Mathlib leaf from the same module: finite limits at line 190 and left adjoint
  at line 157. The full source was read. It requires no new statement module.
- The new definition also uses `def-weil-ring-localization-away`'s recorded
  `Localization.Away`, with the ring structures and `IsLocalization.Away.invSelf`
  from `Mathlib.RingTheory.Localization.Away.Basic` (read signatures/docstrings).
- `SheafOfModules.free` and `ιFree` were read in Mathlib's Sheaf/Free.lean,
  lines 30–85; `ShortComplex.ShortExact` was read in ShortComplex/ShortExact.lean,
  lines 13–45. These are reused without private definitions.

Edge cases checked against the formulas and the source proof: f=0 (localization is
zero, no injectivity of multiplication assumed); nilpotent f; nonzero zero divisors;
f a unit; the zero ring; n=0 and the successor coordinate; the zero sequence and
N=k=M=0 in proof step 4. The partial-sum construction needs the power-torsion
factor f^k, which the docstring preserves. An empty underlying category has no
object U, as in the natural statement, and no artificial nonempty assumption is
added. Empty covering sieves and nontrivial sheafification are covered by the
sheafification unit, rather than incorrectly demanding a globally sectionwise
surjection onto the localization sheaf.

Searches actually run with msearch.py (item search log):

- LeanFinder, `free resolution of a localization sheaf by one minus multiplication shift on countable coproducts`:
  eight hits on free sheaves and generators/presentations, no telescope resolution.
- Loogle, `IsLocalization.Away`: 12 ordinary localization hits, none the sheaf resolution.
- Mathlib grep, `localization.*resolution|telescope|one_sub.*shift`, Algebra: zero hits.
- LeanSearch, `Presheaf of modules obtained by localizing a ring sheaf at a section`:
  unavailable, Internal Server Error; not reported as a negative mathematical result.
- LeanFinder, `presheaf localization of rings at a global section`: eight hits,
  notably TopCat.Presheaf.SubmonoidPresheaf.localizationPresheaf. Its source was read
  at Topology/Sheaves/CommRingCat.lean:70–113: its index category is Opens X, so it
  does not supply localization over an arbitrary slice site.
- Mathlib grep, `awayPresheaf|localizationPresheaf|SectionwiseLocalization|SectionwiseAway`:
  five hits, all in that TopCat file, with the same limitation.
- Local rg of upstream WeilConjectures and project lean/Sheaf for
  `localization.*presheaf|presheaf.*localization|localizationAway|awayPresheaf|localizationSheaf`
  found other categorical localizations and open-immersion extension-by-zero functors,
  not the sectionwise localization at a section. Further search for
  `SliceAwayLocalization|sliceAwayLocalization_free_resolution|sectionwise.*localization|localization.*sectionwise`
  found no matching declaration. A direct node-id search in upstream gave no hit.
- DAG search for `sectionwise localization|presheaf.*localizations|localization presheaf`
  found uses of the notion, not a definition node for this arbitrary-site presheaf.
  Blueprint searches `localization presheaf` and `localization at a section`
  returned zero matches; ancestor command returned def-weil-pbc-completed-pullback.

Validation: both delivered modules were compiled separately, in dependency order,
using scompile.py on the server, nice 19, two threads, 60 seconds per file. Both
passed with no errors or warnings. No local compiler, build, or direct git command
was run. The final dry run is recorded below after checking.

## New nodes

`def-weil-pbc-slice-away-localization` defines a sectionwise localization presheaf
on the slice with its coherent linear coordinates, exactly L in the first proof
step of this item, from the displayed free resolution in Stacks 0997. Its module
is `Sheaf.CategoryTheory.SliceAwayLocalization`. Every data field is supplied by
a value of the structure: a Mathlib presheaf of modules and its coordinate linear
isomorphisms; its restriction field states the exact fraction rule. It neither
redefines the module category nor the ring localization. The existing TopCat
construction is tied to opens of a space and cannot index an arbitrary Over U.
The actual LeanSearch, LeanFinder and grep outcomes are recorded in the new node;
the upstream/project and blueprint searches are detailed above. The item gains
only this definition node in stmt_deps; all other original node fields are preserved.

## Second reading by NO

I independently read the item and new definition node, both delivered modules,
Stacks algebraization.tex Tag 0997 (lemma-hom-from-Af, lines 833–874),
sites-modules.tex definition-ringed-site, and conventions.tex's ring convention.
The source assumes an arbitrary ringed site and a global section, applied here
on the slice; its rings are commutative with identity, allowing the zero ring.
No statement correction was needed and no Lean or node change was needed.

Object/hypothesis/conclusion checklist, against the node:

1. The site and ring sheaf are `{C : Type uC} [Category.{vC} C]`,
   `{J : GrothendieckTopology C}`, and `O : Sheaf J CommRingCat.{u}`.
   Verdict: the same arbitrary ringed site, with the source's ring convention.
   `J.HasSheafCompose` supplies the forgetful change from commutative rings to
   Mathlib's ring sheaves; it adds no property of the section or structure ring.
2. The object and section are `(U : C)` and `(f : O.obj.obj (op U))`.
   Verdict: exactly U and a section over U, rather than a global section over C.
3. The slice and restricted ring are `J.over U` and
   `((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U`.
   Verdict: exactly the slice with section values O(V), not an open-subspace
   special case. I read `Sheaf.over`, `SheafOfModules.overFunctor`, `over`,
   `Hom.over`, and `overMap` in the recorded dependency modules.
4. The category is `ringedSiteModules restrictedRing`. I read the full
   RingedSiteModules module: this transparently abbreviates Mathlib's
   `SheafOfModules`, retaining its linear morphisms and abelian structure.
   `HasSheafify` and `WEqualsLocallyBijective` on the slice are precisely the
   universe-dependent infrastructure used by that dependency and by the
   recorded sheafification functor. They impose no finiteness or geometric
   condition. Object, hom, and coefficient universes are explicitly bound.
5. `∃ L : SliceAwayLocalization O U f` supplies the sectionwise localization
   presheaf. Its `val` is an actual presheaf of modules; `equiv V` is a linear
   equivalence to `Localization.Away (f|V)`; `restriction` specifies the
   restriction of every fraction. Verdict: exactly the presheaf in the node.
   Fractions exhaust the localization, so these coordinates determine its
   restrictions, and any two models are canonically coordinate-isomorphic.
   Existentially supplying the model does not assume its existence as a premise.
6. The third term is `(PresheafOfModules.sheafification (𝟙 _)).obj L.val`.
   Verdict: exactly module sheafification of that presheaf, not sectionwise
   localization incorrectly asserted to be already a sheaf. I read the
   recorded functor, adjunction/unit, left-adjoint instance, and finite-limit
   instance in Presheaf/Sheafification.lean. The proof dependency for exact
   sheafification is usable verbatim through these declarations.
7. Both first terms are `SheafOfModules.free (ULift.{u} ℕ)`. I read `free`,
   `ιFree`, and `isColimitFreeCofan`: these are categorical coproducts of the
   unit ring module. Verdict: exactly the countable sheaf direct sums; ULift
   does not add indices or remove any natural number.
8. `∃ d`, `∃ q`, followed by `∃ h : d ≫ q = 0` and
   `(ShortComplex.mk d q h).ShortExact` gives all three clauses of exactness.
   I read `ShortComplex.ShortExact`: it is exactness plus mono d and epi q.
   Verdict: includes both zeros in the displayed sequence and uses the same
   maps as the formula clauses; no global sectionwise surjectivity is added.
9. For all slice objects V, naturals n, and coefficients a, the d clause is
   `d(ιFree n a) = ιFree n a - ιFree (n+1) ((f|V)*a)`.
   Verdict: on finite sums, coordinate zero is x₀ and coordinate j+1 is
   x_(j+1) - f*x_j, with the final shifted coordinate retained.
10. The q clause is the sheafification-unit image of
    `(L.equiv V).symm (algebraMap _ _ a * invSelf (f|V)^n)`.
    Verdict: exactly a/f^n, and finite sums give the displayed local formula.
    Quantification over all coordinate inclusions determines the morphism by
    the coproduct universal property without requiring global finite support.

New-node review (H12): `def-weil-pbc-slice-away-localization` is a definition
of precisely the presheaf used in the source's resolution. I checked its four
dependencies, source, self-contained statement, empty proof/proof_deps,
mathlib_searches, created/blueprint/lean_audit/chapter/unit fields and lean
record. Its `val`, `equiv`, and `restriction` fields match each clause, with
arrows reversed correctly by the opposite category. No data or internal proof
is supplied by sorry. There are no new dependency modules in this delivery.

Independent searches (H4): LeanFinder query "Cokernel presentation of
localization using countably many generators and relations e_n - f e_(n+1)"
returned eight ordinary `Module.Presentation` cokernel constructions, not
this resolution. Query "Localizing every value of a ring valued functor at a
compatible section defines a presheaf of modules" returned TopCat's
`SubmonoidPresheaf.localizationPresheaf`, its structure maps, and scheme
Tilde constructions. I opened CommRingCat.lean lines 65–114: its index is
`(Opens X)ᵒᵖ`, so it does not supply the arbitrary-site definition. Independent
rg searches in upstream WeilConjectures and project Sheaf for localization
presheaves/resolutions and telescope declarations found no duplicate. I also
opened the project TelescopeColimit and FilteredFreeTelescopeSplitting:
these concern cochain-complex telescopes/quasi-isomorphisms or exhaustions by
monic stages, not this localization sheaf statement. DAG searches for
sectionwise localization and localization presheaf found uses, not an existing
definition of this notion. The first worker's three search kinds, including
the explicitly unavailable LeanSearch service, remain recorded in the new node.

Edge cases: n=0 gives q(a e₀)=a and the required first two coordinates of d.
No nonzero, non-zero-divisor, characteristic, Noetherian, or field assumption
is present: f=0, nilpotent f, arbitrary zero divisors, units and zero rings are
included. The proof plan correctly retains the factor f^k in the kernel
argument, and its M=0 case. The index is fixed ℕ, so an empty index set is not
part of this node. An empty category admits no U, just as in the node; no
nonempty-site hypothesis is added. Empty covering sieves are handled by
sheafification. Every universe and variable is explicitly bound.

H5–H9: the sole theorem body is sorry; the structure has actual supplied
fields; both module and declaration docstrings cite the correct source and
blueprint. The theorem docstring carries all six proof steps, including the
zero-divisor kernel argument and the sheaf coproduct identification. Both
node lean.statement strings occur verbatim as signatures, and every line is
at most 100 characters. No private definitions, notation or local instances.

Validation: scompile.py compiled both sibling files separately on the server,
nice 19, two threads, 60 seconds per file: SliceAwayLocalization 2.0 s,
SliceAwayLocalizationFreeResolution 1.7 s; the dependency RingedSiteModules
was compiled in the private overlay (1.0 s). No errors or warnings. No local
compiler, lake build, live-library edit, or direct git command was used.
