## Worker report

The module `Sheaf.CategoryTheory.RingedSliceExtensionExactness` states
`SheafOfModules.ringedSliceExtension_exact_iff`, with one postponed theorem proof.
No definitions, helper theorems, new nodes, dependency repairs, or statement changes.
Read the item and each statement dependency, their recorded declarations and docstrings,
and the actual source at sites-modules.tex, lemma-j-shriek-reflects-exactness (Tag 0E8G).

Hypotheses and clauses, in order:

- An arbitrary site is `{C : Type u} [Category.{v} C] (J : GrothendieckTopology C)`.
  No precoverage, pullbacks, subcanonical topology, or points are assumed.
- A commutative ring sheaf is `(O : Sheaf J CommRingCat.{max u v})`.
  `sheafCompose J (forget₂ CommRingCat RingCat)` forgets commutativity without
  changing sections, ring operations, restrictions, or the topology.
- `(U : C)` is the arbitrary slice object. `R.over U` is precisely the localized
  ring sheaf on `J.over U`, for the forgotten ring sheaf `R`.
- The coefficient universe is `max u v`, containing both objects and morphisms
  of the site. Ring and module sheaves use that common universe. Object and
  morphism universes remain independent: a site in Type (t+1) with Category.{t}
  is allowed, with coefficients in t+1. This is the usual small-relative-to-modules
  convention of the module-category dependency, not an equality of site universes.
- `S : ShortComplex (CategoryTheory.ringedSiteModules ... (R.over U))` supplies
  all three localized module sheaves `S.X₁`, `S.X₂`, `S.X₃`, the arrows `S.f`,
  `S.g`, and the complex identity `S.zero : S.f ≫ S.g = 0`. Thus it quantifies
  over exactly the complexes of the node, with no exactness assumption.
- `extensionByZeroPresheaf R U ⋙ PresheafOfModules.sheafification (𝟙 R.obj)`
  is exactly j_!, objectwise the sheafification of the specified direct-sum
  extension. Its `.map S.f` and `.map S.g` are precisely j_!a and j_!b.
- `imageSubobject S.f = kernelSubobject S.g` is im(a)=ker(b) as subobjects
  of S.X₂. The right side uses the identical two constructions on the extended
  arrows, as subobjects of j_!(S.X₂). The connective is `↔`, preserving both
  directions. Subobject equality compares the actual embeddings, rather than
  asserting only that the underlying image and kernel objects are isomorphic.

Dependency declarations used:

- `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`, `Sheaf.over`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.over`, `overFunctor`, and `Hom.over` give the recorded localization
  interface. These are available through the public extension-presheaf import.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the recorded transparent abbreviation of Mathlib `SheafOfModules`.
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf` (including its actual direct-sum
  object and restriction construction, read in full).
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` at the identity of R.obj; available through
  the ringed-module category import. Its underlying-abelian comparison and
  adjunction are also the Mathlib match of the module-sheafification proof node.
- Proof imports: `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`,
  `Sheaf.Paper.SiteSheafificationSectionsLocal`, and
  `Mathlib.CategoryTheory.Sites.PreservesSheafification`. The first recorded
  theorem has a small-precoverage presentation; no such extra hypotheses are
  inherited by this statement. Stage 3 may generalize that proof interface or
  use the same direct-sum argument on a general Grothendieck topology.

Edge cases checked against the statement and Tag 0E8G: zero sheaves and zero
arrows are allowed; no maps V→U gives an empty direct sum, hence zero; multiple
maps contribute separate summands, so no subterminal-U assumption has crept in;
empty covering families force zero sections by the sheaf condition; nothing
assumes epimorphisms are surjective on sections or that the unit is an isomorphism.
An empty category has no U and hence no instance of the assertion, as expected.
No injectivity of a or surjectivity of b is imposed (only middle exactness).

Searches for an existing statement (2026-10-15):

- `msearch.py ... leanfinder "Extension by zero on a ringed site slice preserves
  and reflects exactness of module sheaf complexes"`: eight hits, including
  ModuleCat.localizedModule_functor_map_exact, MayerVietorisSquare exactness,
  degreewise exactness, and HomologicalComplex extension. None is the general
  ringed-site slice functor or a preservation-and-reflection equivalence for it.
- `msearch.py ... loogle 'SheafOfModules, "exact"'`: zero hits.
- `msearch.py ... grep 'extensionByZero|jShriek|j_shriek'`: zero Mathlib hits.
- `msearch.py ... leansearch "Extension by zero from ringed site slice reflects
  exactness"`: service unavailable (Internal Server Error).
- `rg` on the read-only upstream WeilConjectures source, both for the node id
  and extension-by-zero names: no matching theorem. `rg` on lean/Sheaf finds the
  existing direct-sum construction and scheme/open and general-site exactness
  results; none states reflection for arbitrary ringed-site slices. In particular
  the exact-adjunction theorem supplies preservation only.
- `rg` of the new full declaration name in Mathlib, upstream, and lean/Sheaf:
  no collision. Read Mathlib ShortComplex.Basic and Subobject.Limits to verify
  the complex, imageSubobject and kernelSubobject signatures.

Server validation: scompile.py compiled this delivered module cleanly (1.9 s,
nice 19, two threads, 60 s per file), resolving RingedSiteModules in its private
overlay. No local compiler or global build was run. Initial elaboration checks
exposed the ring-forgetting API's common-universe requirements; the final file
uses the standard common coefficient universe while keeping site universes separate.
No mathematical node fault or disputed statement found. The declaration docstring
contains all four proof steps, including the local unit-injection argument and
zero-detection applied to the middle homology quotient.


## Second reading by NB

Independently read the node and its four proof steps, the complete delivered module,
Stacks sites-modules.tex, lemma-j-shriek-reflects-exactness (Tag 0E8G), its preceding
extension-by-zero construction and exactness lemma, and the ringed-site definition.
The source assumes an arbitrary ringed site and an object U; there are no hidden
geometric, finiteness, characteristic, point, or subterminality hypotheses.

Object/hypothesis/conclusion checklist (all pass):

1. Site C: `{C : Type u} [Category.{v} C] (J : GrothendieckTopology C)`.
   This is a general site, with independent object and morphism universes. No
   precoverage, pullbacks, small-category equality, or enough-points assumption.
2. Commutative ring sheaf O: `(O : Sheaf J CommRingCat.{max u v})`.
   The explicit `sheafCompose J (forget₂ CommRingCat RingCat)` retains exactly
   its underlying ring sheaf. Commutativity is the node's own hypothesis.
3. Slice object: `(U : C)`, unrestricted. The underlying ring sheaf's `.over U`
   is Mathlib `Sheaf.over` on `J.over U`. Read `GrothendieckTopology.over`:
   covering sieves are exactly those corresponding to covering sieves downstairs.
   Read `SheafOfModules.over`, `overFunctor`, `Hom.over`, and `overMap` for the
   dependency's restriction/relocalization interface. No alternate localization.
4. Module categories: `CategoryTheory.ringedSiteModules.{max u v}` is the recorded
   dependency's transparent abbreviation of `SheafOfModules`, whose objects have
   sectionwise module structures and semilinear restrictions. Read its module,
   including the abelian-category size convention. No privately chosen structure.
5. Three modules G1,G2,G3, arrows a,b, and ba=0: the binder
   `S : ShortComplex (...)` provides exactly `S.X₁`, `S.X₂`, `S.X₃`, `S.f`, `S.g`,
   and `S.zero : S.f ≫ S.g = 0`. Read Mathlib's structure fields. It assumes
   neither exactness nor mono/epi properties of either arrow.
6. Canonical j_!: each occurrence of `extensionByZeroPresheaf ... U ⋙
   PresheafOfModules.sheafification (𝟙 R.obj)` is precisely the node's functor.
   Read the dependency's actual direct-sum sections, semilinear restriction,
   summandwise morphism map, and final functor. Read Mathlib sheafification,
   its underlying-abelian comparison and adjunction: identity ring map gives
   sheafification as O-modules. Thus `.map S.f` and `.map S.g` are j_!a,j_!b.
7. Original middle exactness: `imageSubobject S.f = kernelSubobject S.g`.
   Read Mathlib Subobject.Limits: image is the subobject represented by the
   image inclusion, kernel by the kernel inclusion. Equality compares embedded
   subobjects of G2; it does not merely compare abstract image/kernel objects.
8. Extended middle exactness: the same image/kernel equality on the two mapped
   arrows, in the extended module category. The `↔` states both directions in
   the node's order. There is no extra endpoint-exactness clause.

Edge cases: zero sheaves, zero arrows and the zero ring are permitted. No maps
V→U gives an empty direct sum, hence zero; multiple maps remain distinct summands.
An empty site has no U and the quantified assertion is vacuous. Empty covering
families are allowed; the docstring's local-injection argument uses sheaf
separatedness and remains valid there. There is no n, characteristic, scheme,
or nonempty-index assumption. The common coefficient universe `max u v` contains
both site universes, as required by the module-category dependency and standard
sheafification construction, and permits Type (t+1)/Category.{t} sites. It does
not identify object and morphism universes or impose geometric smallness.

Independent duplicate searches:

- `msearch.py ... leanfinder "Sheafified direct sum on a slice category detects
  exactness of module sheaves"`: eight hits, headed by SheafOfModules.instAbelian,
  followed by condensed/Grothendieck abelian-category results; no equivalence for
  canonical slice extension. Returned signatures are different statements.
- Loogle `"reflects" "exact"` was invalid syntax and supplies no evidence.
  Retried valid `"exact"`: twelve mostly core/tactic/arithmetic name hits;
  no relevant theorem. LeanFinder and the direct searches supply the useful check.
- LeanSearch for exactness iff exactness after slice extension: service unavailable
  (Internal Server Error), recorded as unavailable, not as a negative result.
- Independently ran rg for extensionByZero, jShriek, lowerShriek and
  extension_by_zero in upstream WeilConjectures and project lean/Sheaf, and for
  extensionByZero/jShriek/j_shriek across Mathlib. Mathlib has no named match.
  Read project SiteExtensionByZeroExact and LocalizedModuleAdjunctionExact:
  they give preservation, not this general-site reflection equivalence.
  Upstream lower-shriek matches concern Weil/etale sheaves and special geometric
  settings, not modules on an arbitrary ringed-site slice. Also checked the
  exact declaration name/node id in upstream sources and dag/lean_names_upstream.json:
  no collision or existing theorem.

H5/H6/H8/H9 and delivery scope: no new nodes or dependency modules are delivered;
there are no definitions, hidden data, private/local declarations, or proved helper
lemmas in this module. The single theorem has only `sorry`. Both docstrings cite
0E8G and the correct blueprint id. Its four proof-plan steps match the node:
exactness preserves middle exactness; the distinguished-coordinate unit is monic
by local equality; it detects zero objects; apply this to the cokernel of the
factorization through ker(b). Read the underlying-sheafification comparison too.
The imported exact-adjunction and local-sections proof interfaces currently use
precoverages (the former also SmallCategory); they do not supply hidden assumptions
in this theorem. Stage 3 must generalize those proof interfaces or prove the same
local/direct-sum argument directly for a Grothendieck topology. They are proof
imports, not unusable statement-dependency constructions requiring a module here.

No mathematical mismatch found; kept the Lean and node unchanged. Appended this
independent reading only. Mechanically verified lean.statement equals the source
signature verbatim, all variables/universes are bound, and lines are at most 100
characters. Recompiled with the required scompile.py server command: the side
RingedSiteModules overlay compiled in 1.0 s and this module in 1.9 s, nice 19,
two threads, 60 seconds per file; no errors or warnings were emitted.
