## Worker report

Item: `lem-zl-finite-fp-proetale-pushforward-exact`, group NH, stage 2.
The module `Sheaf.AlgebraicGeometry.FiniteFpProEtalePushforwardExact` states
`AlgebraicGeometry.Scheme.finite_fp_proEtale_pushforward_exact`, with proof `sorry`.
It adds no definitions and makes no statement correction.

The source was read at `literature/stacks-project/proetale.tex`, lines 4762--4784,
Tag 09A8, `lemma-finite`: finite and locally of finite presentation, followed by
exactness on all pro-etale abelian sheaves. The module consequence in the node
follows by forgetting module structures, as in its proof step 5.

Clause-by-clause correspondence:

- Schemes and the map are `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Finiteness is `[IsFinite f]`; local finite presentation is
  `[LocallyOfFinitePresentation f]`. Neither is replaced by finite etaleness,
  flatness, or a condition on the base scheme.
- The original small sites are `ProEt.topology X` and `ProEt.topology Y`.
  Their object universe is `u+1` and their Hom universe is `u`. We use these
  original sites, with no universe equality or restriction of objects.
- The abelian direct image is `proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}`.
  The first two conjuncts are `PreservesFiniteLimits` and `PreservesFiniteColimits`
  of this functor. For an additive functor between abelian categories this is
  equivalent to exactness, and in particular says that every short exact sequence
  remains short exact. The canonical direct image is sectionwise and additive.
- The general coefficient clause universally quantifies
  `R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}` and
  `R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1}`. These are arbitrary ring
  sheaves, not just constants or finite rings.
- The specified ring map is
  `c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ⟶ R_X`.
  Its mate is exactly
  `(proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv R_Y R_X c`.
  This is the canonical map `R_Y ⟶ f_* R_X`; it is not an arbitrary chosen map.
- The module functor is Mathlib's `SheafOfModules.pushforward.{u + 1}` with
  `F := proEtaleBaseChange f`. Its `S` parameter is the ring sheaf underlying
  `R_Y`, its `R` parameter the ring sheaf underlying `R_X`. The ring map is the
  preceding mate under `sheafCompose ... (forget₂ CommRingCat RingCat)`.
  Thus at a target object V the module is the given module on `V ×[Y] X`, with
  scalar action through the mate, exactly as the node and the module-adjunction
  dependency specify. The two last conjuncts express finite-limit and
  finite-colimit preservation on the whole category of these module sheaves.
- No binder restricts modules by constructibility, torsion, flatness, finite
  generation, or finite presentation; no assumption says `c` is invertible.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`: affine with finite maps on affine sections.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`: the affine-local finite
  presentation property, including `finitePresentation_appLE`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`
  and `ProEt.topology`: weakly etale objects and the specified topology.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`,
  `SheafOfModules.module_pullback_pushforward_adjunction`: the general
  ringed-topos module adjunction, including its explicit action through the
  adjunct. Its module is imported as required. The statement instantiates the
  canonical site-based Mathlib construction directly and therefore needs no
  existentially chosen module functor or specialized universe interface.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  `proEtaleBaseChange`, `proEtaleSheafDirectImage`,
  `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`, in namespace
  `AlgebraicGeometry.Scheme`: these supply the canonical maps used in the
  signature. `def-weil-proetale-inverse-image` already had this landed record;
  it was promoted from an existing proof dependency to a statement dependency.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.pushforward`: the existing sectionwise module pushforward,
  restricting scalars along its input map. It is reached through the imports.

All recorded proof dependency modules are imported (plain imports when used
only for the proof): source-locality and affine finite presentation via the
Mathlib modules; pro-etale site and covering via the site module;
`exists_isWContractibleRing`, `RingHom.indEtale_principalZariski_stability`,
`isWContractibleRing_of_finite_finitePresentation`,
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`,
`AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_of_iso`,
`CategoryTheory.moduleSheaves_colimits_forgetful`, and the inverse-image module.
The constant-coefficient module-direct-image dependency is a declaration of
that same inverse-image module. The missing/stale local file
`Sheaf.RingTheory.FiniteWContractible` was read through the prescribed
`scompile.py --source Sheaf.RingTheory.FiniteWContractible`, not duplicated.

Edge cases checked before writing: empty X, empty Y (then any map has empty X),
empty fibres and zero fibre rings; identity morphisms; the zero coefficient ring
and zero modules; arbitrary nonconstant and infinite coefficient sheaves;
noninvertible maps c. The source's w-contractible proof explicitly includes
C=0. For f the identity the module clause includes restriction of scalars along
any ring-sheaf map, which is exact; this checks why an isomorphism binder for c
would have been incorrect. Finite closed immersions of finite presentation are
included, without any flatness condition. All variables and the universe u are
explicit; `autoImplicit` is false.

Searches for an existing statement, 2026-10-18:

- `msearch.py ... leanfinder "Direct image of abelian sheaves on the small
  pro-etale site along a finite locally finitely presented morphism is exact"`:
  eight hits, including LightCondensed Grothendieck abelian, condensed exact
  (co)limits, Mayer--Vietoris short complexes and general sheaf exact limits;
  none states finite pro-etale pushforward exactness.
- `msearch.py ... loogle "CategoryTheory.Sheaf, AlgebraicGeometry.IsFinite"`:
  zero hits.
- `msearch.py ... grep "pro[Ee]tale.*(exact|finite)|(exact|finite).*pro[Ee]tale"`:
  only two lines in `Mathlib/AlgebraicGeometry/Sites/Proetale.lean` using `exact`
  in proofs, no matching theorem.
- `msearch.py ... leansearch "A finite locally finitely presented morphism of
  schemes induces an exact direct image on small pro-etale abelian sheaves"`:
  eight hits, all finite-morphism/finite-presentation definitions, projections
  or affine section lemmas, none the requested theorem.
- `rg` of pro-etale pushforward and exactness in the named upstream checkout,
  the framework under the shared `lean/WeilConjectures`, and `lean/Sheaf`:
  found existing inverse-image/direct-image constructions, constant-module
  left exactness, closed-support specializations and finite-etale statements;
  none handles arbitrary finite locally finitely presented f and arbitrary
  ring-sheaf coefficients. In particular `proEtaleRingModuleDirectImage` in
  `ProEtaleOperations` takes an isomorphism c, so it does not express this
  node's general clause. We use the existing Mathlib pushforward directly.
- `rg -n 'lem-zl-finite-fp-proetale-pushforward-exact'` in the named upstream
  `WeilConjectures` source found no recorded declaration.

No STATEMENT-DISPUTED flag, new notion, hollow data, or dependency repair.
The sole postponed theorem has the matching item node and a five-step source
proof in its docstring.

## Second reading by NH

I reread the node and the completed signature as a separate self-check; the
maintainer provides the independent review under the dispatcher's protocol.
The two geometric hypotheses agree with Tag 09A8. Both abelian and module
clauses quantify over the full categories. The direct image is along the
recorded base-change functor, with direction from X sheaves to Y sheaves.
I checked the source/target ring parameters of `SheafOfModules.pushforward`
and the direction of `homEquiv`: its input is the given inverse-image map c,
and its output is `R_Y ⟶ f_* R_X`. Forgetting commutativity preserves that map.
This retains every ring map, including nonisomorphisms. Both exactness halves
are present in each clause, so the short-exact-sequence consequence is not
weakened to mere left exactness. No universe equality is introduced. No
mismatch requiring a statement correction or dependency repair was found.

Validation: the prescribed `scompile.py NH
lem-zl-finite-fp-proetale-pushforward-exact <module>` passed both sandbox and
library compilation with no errors or warnings (sandbox 9.5 s, library 58.6 s).
The node record's statement was checked against the exact file signature;
the file has one theorem, one `sorry`, and no lines over 100 characters.
