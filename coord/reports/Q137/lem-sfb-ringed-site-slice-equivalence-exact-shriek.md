## Worker report

Stage 2, Q137: the module `Sheaf.CategoryTheory.RingedSiteSliceExactShriek` states
`CategoryTheory.exists_exact_moduleLeftAdjoint_of_sliceEquivalences`, with a sole
`sorry` proof. No definition or proof is introduced. The accepted stage-1 split
and all node fields other than `lean` are retained. The inherited BLOCKED was
about an already completed stage-1 split. Q39's `reviewed.result = pass` and the
22:49 ledger entry are stage 1; the live item has neither `lean` nor
`reviewed_lean`. Brief-stage2 section 0 explicitly permits this stage handoff.

Clause-by-clause correspondence:

- Size convention: `C : Type c`, `Category.{vc} C`, `D : Type d`,
  `Category.{vd} D` bind all size levels independently. Every site is small
  relative to the coefficient/module universe `max c d vc vd r`. The additional
  level `r` permits enlargement. No object/morphism universe equality is imposed.
- Small sites: `J : Precoverage C`, `K : Precoverage D` and
  `hJ : J.IsSiteForCoverings`, `hK : K.IsSiteForCoverings` use the recorded
  actual-covering site axioms; sheaves use the generated Grothendieck topologies.
  In particular, there is no extra `IsStableUnderComposition` instance that
  could exclude finite coverings.
- The functor is `F : C ⥤ D`. Continuity in the covering sense is `hcover`:
  each covering presieve maps to a covering presieve. The second continuity
  condition of 00WV, preserving pullbacks of covering arrows, is contained in
  `PreservesLimitsOfShape WalkingCospan F`. The `F.IsContinuous` binder supplies
  Mathlib's sheaf-precomposition interface; it follows from these hypotheses
  and the site axioms and is not an additional mathematical restriction.
  Cocontinuity is `F.IsCocontinuous J.toGrothendieck K.toGrothendieck`, the exact
  generated-topology version used by the recorded special-cocontinuity interface.
- Commutative coefficient sheaf is `R : Sheaf K.toGrothendieck CommRingCat`.
  `sheafCompose ... (forget₂ CommRingCat RingCat)` only forgets commutativity,
  retaining the original sections, ring operations and restrictions.
- `R' = R composed with F` with original restriction maps is exactly
  `(F.sheafPushforwardContinuous RingCat ...).obj` of that ring sheaf.
- Fibre products and equalizers in C are `HasPullbacks C`, `HasEqualizers C`.
  Their preservation is `PreservesLimitsOfShape WalkingCospan F` and
  `PreservesLimitsOfShape WalkingParallelPair F`. Target limits are only needed
  on the images of these diagrams, supplied by preservation; no global target
  limits or terminal object is assumed.
- The induced slice functor is Mathlib's `Over.post (X := X) F`.
  `hslice` says it is an equivalence of categories at every X.
- `hsliceCover` quantifies over every object Y of `Over X` and every presieve P
  on it. A family covers the induced slice precisely when its underlying family
  `Presieve.functorPushforward (Over.forget X) P` is in J. The right side is the
  identical condition for `P.map (Over.post F)` in the target slice. This is the
  node's covering if and only if, for the actual families, not merely an arbitrary
  chosen topology or a global equivalence of the sites.
- Restricted ring sheaves coincide sectionwise: at `(c' -> c)` both have R(F c'),
  and on a slice morphism both use R(F of its underlying arrow). This introduces
  no extra ring-isomorphism hypothesis or arbitrary structural ring map.
- The categories in both directions are the dependency's `ringedSiteModules`,
  transparently Mathlib `SheafOfModules`. The existential L has exactly the
  direction Mod(C,R') to Mod(D,R).
- T is `SheafOfModules.pushforward (F := F) (𝟙 _)` with the identity map of the
  precomposed ring sheaf. Its presheaf data are precomposition, including the
  original restrictions and sectionwise linear maps. There is no scalar twist.
- Additivity is `∃ hL : L.Additive`. `Nonempty (L ⊣ T)` is the natural Hom
  bijection in both module variables, including both naturality conditions.
- Exactness is the final universal implication over every `ShortComplex` S of
  source module sheaves: `S.ShortExact` implies `(S.map L).ShortExact`. The
  explicit zero-preservation witness is exactly the one derived from hL, to
  avoid a local notation or local instance. `ShortExact` means mono, exact at
  the middle object, and epi. No finite-limit strengthening is asserted.

Dependencies read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings` gives the actual site axioms.
- `WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`,
  `CategoryTheory.Functor.IsSpecialCocontinuousForCoverings` was read in full.
  Only its first cocontinuity clause and its continuity clauses apply here;
  the theorem does not assume the stronger special-cocontinuity predicate.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`
  is used for the two module categories, with the inherited Mathlib structures.
- The size-convention dependency is a convention record, represented by the
  explicitly bound universe levels, not an import or a duplicated definition.
- Mathlib `SheafOfModules.pushforward`, `Over.post`, `Functor.IsContinuous`,
  `Functor.IsCocontinuous`, `ShortComplex.ShortExact`, `ShortComplex.map`, and
  `Functor.preservesZeroMorphisms_of_additive` supply the canonical constructions.
  `Mathlib.Algebra.Category.Ring.Limits` supplies the existing limit-preserving
  coefficient-forgetful functor needed by `sheafCompose`.
- The stated Mathlib proof dependency `def-pur-localized-ringed-site` is supplied
  by the imported `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
  and its `Sites.Over` import. The other proof dependency,
  `lem-sfb-local-slice-module-shriek-exact`, currently has no Lean record/module;
  therefore it cannot yet be imported. It is named in the proof docstring and
  is not needed to state this theorem. No downstream dependency wait is created.

Sources read: `sites-modules.tex` lemma-exactness-lower-shriek (04BH),
lemma-lower-shriek-modules (0797), remark-when-shriek-equal (0798), including
its equation-compare-on-localizations. These agree with the accepted proof plan:
0797 gives the module left adjoint, 0798 identifies its underlying abelian
functor using the slice ring equivalences, and 04BH gives exactness.

Edge cases checked before writing: F the identity; slice localization
`Over.forget U`; zero coefficient rings; zero modules; empty covering families;
empty C (the zero extension is left adjoint to the unique restriction); empty D
(then C is empty if F exists). None requires a terminal object in C or D, a
nonempty site, nonzero ring, a global equivalence F, or extra target limits.
Empty families are permitted in `hsliceCover`. No statement dispute or
source correction was needed.

Searches actually run via the prescribed msearch.py wrapper:

- leanfinder: "Exact additive left adjoint of precomposition of sheaves of
  modules for a continuous cocontinuous functor inducing equivalences on slices".
  Eight hits, including `Functor.sheafAdjunctionCocontinuous`,
  `SheafOfModules.pushforwardPushforwardAdj`, `PullbackConstruction.adjunction`,
  `pullbackPushforwardAdjunction`. Read the generic module adjunction source;
  it does not state the slice-equivalence exactness criterion.
- leansearch: "Exact left adjoint of restriction of sheaves of modules when
  all induced slice site functors are equivalences". Eight hits: scheme-open
  restriction adjunctions, scalar restriction, sheafification, and generic
  module pullback. None is the node's general exactness criterion.
- loogle: "SheafOfModules.pushforward, Functor.Additive,
  ShortComplex.ShortExact" returned no hits, reporting unknown identifier
  Functor.Additive. This query is inconclusive, not evidence of absence.
- grep: "lowerShriek|lower_shriek|exact" in
  Algebra/Category/ModuleCat/Sheaf: 16 hits, ordinary proof lines and generic
  constructions; no criterion for exact lower shriek under slice equivalences.
- Local rg across `lean/Sheaf`, `lean/WeilConjectures` and
  `dag/lean_names_upstream.json` for slice equivalences, lower shriek and exact
  adjoints found generic ringed equivalence and scalar adjoints, and geometric
  lower-shriek results. They do not give this statement for arbitrary sites.
  The node-id grep in `lean/WeilConjectures` found no match. No existing exact
  declaration or duplicate notion was found. A guessed Mathlib Over.lean path
  was absent; the actual `Comma/Over/Basic.lean` and `Sites/Over.lean` were read.

Validation: scompile.py compiled the sandbox and final library-module versions
cleanly (2.4 s and 2.5 s), with the normal 60 s limit. Earlier probes diagnosed
an omitted ring-limits import and an explicit Additive witness needed for
mapping short complexes. The delivered module uses no raised heartbeat option.

## Second reading by Q137

The dispatcher prohibits starting other agents. This is an author rereading,
not an independent review; the maintainer supplies the independent reading.
I reopened the node and final file and matched each binder and conclusion above.
The critical checks were the direction L ⊣ T, the identity structural ring map,
the actual covering iff on every slice, preservation of equalizers without a
terminal object, and short exactness rather than sectionwise surjectivity.
The file states only the requested existence, additivity, adjunction and
short-exact-sequence preservation. No accepted statement field changed.

## Maintainer review FIX (2026-10-24)

`hsliceCover` used `Presieve.functorPushforward (Over.forget _)`. In Mathlib
(`Sites/Sieves.lean:406`) that is the downward-closed generated presieve
`{h ≫ F.map g | g ∈ P}`, not the image family. The hypothesis therefore asked whether
generated sieves belong to the non-saturated precoverages `J`, `K`. It did not ask about the
node's actual families: "a family covers if and only if its image covers". The binder now reads
`P.map (Over.forget X) ∈ J Y.left ↔ (P.map (Over.post F)).map (Over.forget (F.obj X)) ∈ K (F.obj Y.left)`.
The docstring sentence and `lean.statement` were updated to match. Nothing else changed.
