## Worker report

The delivery states `AlgebraicGeometry.Scheme.ProEt.weaklyEtale_localization` in
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`. Its only proof is `sorry`.
No definition is introduced, no node statement is corrected, and only the item's `lean`
field changes. There are no dependency replacements or new nodes.

Hypotheses and universes:

- `X : Scheme.{u}` is the arbitrary ambient scheme. `W : X.ProEt` bundles the scheme
  `W.left`, its map `j = W.hom`, and its weakly etale property. Thus both the object
  hypothesis and the weakly etale hypothesis are supplied, without another bounded site.
- `A : CommRingCat.{u + 1}` is a commutative coefficient ring in the containing universe.
  `RingCat.of A` retains its ring operations. This is the ring-valued constant sheaf
  presentation explicitly permitted by def-weil-pbc-constant-sheaf; it does not replace
  the module category by sheaves of modules over a constant presheaf.
- `u`, `v`, `w`, all objects and all morphisms are explicitly bound. The sites use the
  same `Scheme.{u}` bound on both sides. Modules and coefficient rings live in `u+1`.
  The auxiliary sheaf-value category has arbitrary object and morphism universes `v,w`.
  No independently chosen small skeleton or a smaller test universe is assumed.

Clause (1):

- `∀ V : W.left.ProEt, WeaklyEtale (V.hom ≫ W.hom)` states closure under composition.
- `∀ T : Over W, WeaklyEtale T.hom.left` states the converse permanence assertion for
  every arrow of the ambient slice, rather than assuming it separately.
- `∃ e : Over W ≌ W.left.ProEt` supplies the canonical site equivalence, oriented opposite
  to the node's iota. Its inverse is iota. The four subsequent `HEq` clauses specify the
  actual structure arrows and underlying morphisms on both sides: `e.functor` reads
  `T.hom.left`, and `e.inverse` reads `V.hom` as the arrow to `W`. Heterogeneous equality
  avoids transporting domain schemes between equal records; it identifies those domains
  as well as the arrows. The triangle in the ambient `Over W` object then says that its
  structure map to X is exactly `V.hom ≫ W.hom`. On maps the two HEq clauses say that
  neither assignment changes the underlying scheme map. Thus this is the concrete
  identification from the node, not an unspecified equivalence of unrelated categories.
- The sieve-membership iff along `S.functorPushforward e.inverse` identifies the two
  Grothendieck topologies. The same underlying arrows on both sides have the same fpqc
  finite-affine-cover condition (the `ProEt.precoverage` definitions), so it is also the
  asserted identification of covering families.
- For every value category `D`, the existential sheaf equivalence `s` has the functor
  equality `s.functor ⋙ sheafToPresheaf = sheafToPresheaf ⋙ whiskeringLeft ... e.inverse.op`.
  This specifies restriction on objects, transition maps, and morphisms, not just abstract
  equivalence of the sheaf categories. Mathlib's concrete bounded sites are used directly;
  the usual skeletal versions follow by equivalence rather than strict equality of
  independently selected objects.

Clause (2):

- The existential sheaf `R` has underlying presheaf fixed by `hR` to
  `e.inverse.op ⋙ (A_X.over W).obj`. Thus it is precisely `A_X|_W` under the identification,
  including its transition maps. `Sheaf.over` is the recorded localized ringed-site notion.
- `c : A_W ≅ R` is an isomorphism of sheaves of rings, with the displayed constant sheaves
  constructed using `constantSheaf` in `RingCat` on the two recorded topologies.
- For each object `V`, the first unit equation uses `HEq` to compare the composite of the
  W-site constant-presheaf unit with `c.hom.hom.app (op V)` and the X-site unit evaluated
  at `(e.inverse.obj V).left`. These are precisely the maps from the coefficient ring
  sending `a` to its constant section. This says identity on every constant section.
- The following universal clause takes every sheaf-of-rings map `f : A_W ⟶ R` having
  those same composites and concludes `f = c.hom`. This supplies the stated uniqueness,
  beyond the existence of an abstract ring-sheaf isomorphism.

Clause (3):

- `q : ringedSiteModules (A_X.over W) ≌ ringedSiteModules A_W` identifies the two recorded
  module-sheaf categories. The equality after `SheafOfModules.forget` requires its functor
  to be exactly `PresheafOfModules.pushforward (F := e.inverse)
  (c.hom.hom ≫ eqToHom hR)` on the underlying module presheaves. The latter is Mathlib's
  precomposition and restriction-of-scalars construction: sections are the old sections
  at the underlying ambient object, ring action is through c, transition maps are the
  old transition maps, and morphisms have the old components. All of these are fixed
  together by the functor equality, not merely by isomorphic section groups.
- The asserted ambient restriction functor is the existing expression
  `SheafOfModules.overFunctor A_X W ⋙ q.functor`. It is a functor with source
  `ringedSiteModules A_X` and target `ringedSiteModules A_W` without an additional axiom
  or helper definition. The equivalence q gives exactly the second assertion of (3).

Clause (4):

- `IsOpenImmersion W.hom → ...` makes this clause conditional on precisely the additional
  open-immersion hypothesis. It is not imposed on clauses (1)--(3).
- `Mono W.hom` is the categorical monomorphism conclusion.
- `∀ V : X.ProEt, Subsingleton (V ⟶ W)` gives at most one ambient X-morphism to W.
- The first iff compares `Nonempty (V ⟶ W)` with the existence of a scheme map
  `a : V.left ⟶ W.left` satisfying `a ≫ W.hom = V.hom`, exactly factorization through j.
- The second iff compares the same existence with
  `Set.range V.hom ⊆ Set.range W.hom`, exactly the set-theoretic image criterion.

Dependencies used and inspected:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, whose full definition uses the
  existing `Scheme.ProEt`, `ProEt.topology`, constant sheaf and `SheafOfModules` encoding.
  The current statement uses those same concrete sites; it does not need a derived category.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.precoverage`,
  `ProEt.topology`, `ProEt.mk`, and `ProEt.forget` (site notions underlying that dependency).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `IsOpenImmersion.mono`, `IsOpenImmersion.lift`, `lift_fac`, `lift_uniq`.
- `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`, `Sheaf.over`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`. These are the exact recorded localization interfaces.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`;
  `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the landed
  transparent abbreviation of Mathlib's `SheafOfModules`. This is the dependency's current
  general-site interface, not the obsolete scheme-only declaration.
- Proof infrastructure is imported for ring-sheafification compatibility in
  `Mathlib.CategoryTheory.Sites.CoverLifting`, with
  `Functor.pushforwardContinuousSheafificationCompatibility` and
  `Functor.toSheafify_pullbackSheafificationCompatibility`; `WeaklyEtale.of_comp` and the
  composition/base-change instances are available through the imported pro-etale site.
  The size convention is metatheoretic and has no module to import.

Source and edge-case checks:

Read Stacks `proetale.tex`, Definition 09AE (restriction for every weakly etale j), and
`more-morphisms.tex`, weakly etale composition and permanence (094T and 0951), together
with the recorded localized-site definition and the exact Mathlib restriction interfaces.
An open immersion is only an example in (1); the theorem retains arbitrary weakly etale j.
The empty scheme is allowed for X, W, and every V. Empty covering families are allowed by
sieve membership and the original precoverage, with no nonempty or surjectivity hypothesis
added. The zero coefficient ring is allowed (`CommRingCat` has no nontriviality constraint).
There are no reducedness, separatedness, finite type, quasi-compactness of j, or field
hypotheses. The fpqc condition is on coverings, not an added property of j. Multiple maps
V to W are allowed unless j is open; no monomorphism is asserted in the weakly etale case.
The range formulation covers nonliteral open subschemes as well as open inclusions.

Searches for a pre-existing declaration:

- `msearch.py ... leanfinder` query: "The small pro etale site of a weakly etale scheme is
  the slice site and constant ring sheaves restrict to constant sheaves". Eight hits,
  all on the etale site and its forgetful functor; no exact match.
- `msearch.py ... loogle` query: "AlgebraicGeometry.Scheme.ProEt, CategoryTheory.Over,
  CategoryTheory.constantSheaf". Zero hits.
- `msearch.py ... grep` query `overEquiv|overSheafEquiv` under `AlgebraicGeometry/Sites`.
  Six infrastructure hits, no localization theorem for ProEt.
- `msearch.py ... leansearch` query: "Localization of the pro etale site of a scheme at a
  weakly etale object preserves constant ring sheaves and module sheaves".
  Service unavailable: Internal Server Error. The other search kinds and source inspection
  were used; this unavailable search is not evidence of absence.
- `rg` in the slopmaster2 project, side `lean/Sheaf`, and the side pro-etale framework for
  `weakly.etale.localization|ProEt.*overEquiv|overEquiv.*ProEt` and the item id found no
  matching declaration. The lone relevant framework hit was a use of `Sieve.overEquiv`
  in `AlgebraicGeometry/ProEtale/Comparison/Affine.lean`, not this result.
- The additional project-source searches found `Scheme.Etale.overEquiv` and
  `Etale.overSheafEquiv` in `WeilConjectures/Mathlib/AlgebraicGeometry/Sites/EtaleOver.lean`.
  Read the definitions and signatures: these have Etale objects and jointly surjective
  etale covers, so they do not state this node. Proetale.lean supplies continuity of the
  localization functor but not the slice equivalence with the coefficient/module clauses.
- `grep -rn` for the item id in upstream `WeilConjectures` had no hits. The upstream name
  index and `lean/Sheaf` also had no conflicting `weaklyEtale_localization` declaration.

Validation: the server-only `scompile.py` compiled the delivered module cleanly (2.6 s,
using nice 19, two threads, the unchanged 60 s per-file limit). No local Lean invocation,
Lake build, proof construction, source modification, or live-library write was performed.


## Second reading by NF

I independently read the sandbox node and full Lean statement, all five statement
dependencies and their recorded signatures, the proof-dependency records, and the
source passages: proetale.tex Definition 098K and Definition 09AE;
more-morphisms.tex Lemmas 094T and 0951; sites.tex Section 00XZ;
sites-modules.tex Section 03DH and Definition 04IX. None assumes Noetherianity,
separatedness, finite type, a field, or quasi-compactness of j. Definition 09AE applies
to every weakly etale j, not just an open immersion.

Object/hypothesis/conclusion checklist, in the order of the node:

- Arbitrary scheme X: `X : Scheme.{u}`. Pass.
- Arbitrary commutative coefficient ring A: `A : CommRingCat.{u + 1}`.
  `RingCat.of A` uses its actual ring operations, and `constantSheaf` is the recorded
  generic sheafification definition. This ring-valued presentation is explicitly
  allowed by def-weil-pbc-constant-sheaf. Pass.
- Scheme W, structure map j, membership in X_proet, and weak etaleness:
  `W : X.ProEt`, `W.left`, `W.hom`, and the Mathlib instance `WeaklyEtale W.hom`.
  `ProEt` is the full bounded weakly etale over-category, not an affine-only site.
  No additional hypothesis is introduced. Pass.
- Clause (1), composition: `∀ V : W.left.ProEt, WeaklyEtale (V.hom ≫ W.hom)`.
  Clause (1), cancellation: `∀ T : Over W, WeaklyEtale T.hom.left`.
  These are conclusions, not assumptions. Pass.
- Clause (1), concrete canonical equivalence: `∃ e : Over W ≌ W.left.ProEt`.
  Its inverse has the orientation of iota_j. The two new object-equality clauses fix
  `(e.functor.obj T).left = T.left.left` and `(e.inverse.obj V).left.left = V.left`.
  The four original HEq clauses fix structure arrows and scheme maps in both
  directions; the slice triangle fixes the composite structure arrow to X.
  Found and repaired a precision gap: HEq of arrows alone should not be used as
  an assertion that the underlying source schemes are equal. Explicit scheme
  equalities now express that part of the node. With these equalities the concrete
  assignments preserve the objects and maps as required, independently of proofs
  stored in object records. Pass after repair.
- Clause (1), coverings: the sieve-membership iff for `S.functorPushforward e.inverse`
  identifies `topology W.left` with `(topology X).over W`. Read `ProEt.precoverage`
  and `GrothendieckTopology.over`: these are the fpqc weakly etale covers and the
  slice topology specified by the node. Pass.
- Clause (1), sheaves: for every `D : Type v` with `[Category.{w} D]`, the equivalence
  s has its underlying functor exactly precomposition by `e.inverse.op`, via the
  equality after `sheafToPresheaf`. This fixes sections and transition maps, not
  just an abstract equivalence. Pass.
- Clause (2), restricted ring: hR fixes R.obj to the precomposition of
  `(constantSheaf ... (RingCat.of A)).over W`, including all transitions.
  `c : A_W ≅ R` is a ring-sheaf isomorphism. The first family of unit equations
  sends every coefficient to the corresponding constant section. The universal
  clause for every f with those equations gives `f = c.hom`, so uniqueness is
  present. Read `constantSheaf`, `toSheafify`, and `Sheaf.over`; they are exactly
  sheafification of the constant presheaf and sectionwise localization. Pass.
- Clause (3), module equivalence and restriction: q has source
  `ringedSiteModules (A_X.over W)` and target `ringedSiteModules A_W`.
  Its equality after `SheafOfModules.forget` fixes the underlying functor to
  `PresheafOfModules.pushforward (F := e.inverse) (c.hom.hom ≫ eqToHom hR)`.
  Read `pushforward`, `pushforward₀Obj`, and `restrictScalars`: these retain section
  groups and transition maps, pull actions back along c, and retain morphism
  components. Ambient restriction is the well-typed existing composite
  `SheafOfModules.overFunctor A_X W ⋙ q.functor`. There is no missing existence
  axiom for this functor. Pass.
- Clause (4), additional open hypothesis: the implication `IsOpenImmersion W.hom →`
  confines this hypothesis to clause (4). Its conclusions `Mono W.hom`,
  `∀ V, Subsingleton (V ⟶ W)`, the existential-factorization iff, and the range
  containment iff express respectively monomorphism, uniqueness, factorization,
  and the point-set criterion. Read `IsOpenImmersion.mono`, `lift`, `lift_fac`, and
  `lift_uniq` in Mathlib; they cover arbitrary open immersions, including ones
  not presented as literal subset inclusions. Pass.

Dependency audit: opened ProEtaleDerivedCategory.lean and RingedSiteModules.lean.
The former imports Mathlib's `Scheme.ProEt` and `ProEt.topology`; no derived-category
construction is needed in this theorem. The latter is a transparent abbreviation
of Mathlib `SheafOfModules` for general ringed sites, not a scheme-only substitute.
Read the localization and module interfaces in Mathlib Sites/Over.lean and
ModuleCat/Sheaf/PushforwardContinuous.lean, as well as the ring-sheafification
comparison and unit equation in Sites/CoverLifting.lean. The cancellation lemma
`WeaklyEtale.of_comp` assumes exactly weak etaleness of the composite and of the
second map. No dependency replacements or new nodes are needed.

Read coord/pefw-upstream-framework.md and the exact side-framework module
ConstructibleSheaf/ProEtaleModule/Def.lean. Its internal module-object categories
serve the condensed coefficient targets; they do not replace this node's recorded
ordinary ring-sheaf/module-sheaf definitions or provide the complete localization
statement. Inspected upstream EtaleOver.lean: its equivalences concern Etale objects
and etale covers, so they do not state this pro-etale theorem.

Edge cases: empty X, W and V are admitted; the range criterion for empty W says
exactly that V is empty. The empty covering sieve remains admissible wherever the
original topology permits it (Mathlib `ProEt.bot_mem_topology`). No nonempty index
assumption is imposed. The zero ring is included. Characteristic is unrestricted;
there is no integer n. Both sites use Scheme.{u}, so tests have the same bound.
Coefficient rings/modules live in u+1, containing the bounded site. The arbitrary
value category uses independent v,w without a sheafification assumption; equivalence
of sites transports its sheaves without needing sheafification in D. Every universe
and variable is explicitly bound.

Independent searches used different wording from the first worker:

- LeanFinder: "weakly etale slice categories equivalence preserving covering sieves
  and sheaves of constant ring modules". Eight hits, chiefly Etale.forget and etale
  topology, plus algebraic formal-etaleness results; no exact match.
- Loogle: `"ProEt", "Over"`. Twelve infrastructure hits, including
  ProEt.precoverage, the forgetful functor instances, and proetalePrecoverage;
  no complete theorem.
- LeanSearch: "A weakly etale object W over X identifies the pro etale site of W
  with the localized site at W, compatibly with constant coefficients".
  Service unavailable (Internal Server Error); not used as evidence of absence.
- rg on Mathlib, upstream WeilConjectures, side lean/Sheaf and lean/WeilConjectures
  for `ProEt.*[Oo]ver|[Oo]ver.*ProEt|weaklyEtale_localization|pro[Ee]tale.*[Ll]ocaliz`
  located the generic iterated-slice infrastructure, the affine comparison's use
  of it, and pro-etale continuity results. The narrower full-statement name and
  overEquiv search found no matching declaration. Read the relevant EtaleOver
  definitions to rule out the similar etale theorem.

The only Lean repair adds the two underlying-scheme equalities and updates the
explanatory docstring. The node's lean.statement was regenerated verbatim from
that signature. The node's mathematical statement, dependencies, and proof remain
unchanged, so there is no statement correction or citer audit to perform. No new
notion or hollow definition is introduced; the sole proof remains `sorry`.
The source-tagged docstring gives all five proof steps. All lines are at most
100 characters, and no private notation, local instance, or auto-implicit is used.

Second-reader validation: scompile.py compiled the delivered module cleanly in
2.8 seconds (nice 19, two threads, 60 seconds per file), with no warnings.
The overlay also compiled the imported RingedSiteModules dependency in 1.0 second.
The initial run exposed one overlong docstring line, which was wrapped and rechecked.
No local compiler, lake build, git command in the read-only repository, or upstream
source modification was used.
