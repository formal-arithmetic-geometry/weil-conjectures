## Worker report

The module `Sheaf.AlgebraicGeometry.StalkInternalHomFinitePresentation` states
`AlgebraicGeometry.RingedSpace.exists_stalk_internalHom_linearEquiv_of_finitePresentation`.
It has one theorem with `sorry` and no definitions. The node is unchanged except for `lean`.

Hypothesis and conclusion correspondence:

- The ringed space `(X, O_X)` is `(X : RingedSpace.{u})`, Mathlib's sheafed space of
  commutative rings. No scheme, locality of stalk rings, or Noetherian assumption is imposed.
- The two O_X-modules F and G are the binders `F G : SheafOfModules.{u}` over
  `((sheafCompose (Opens.grothendieckTopology X)
  (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)`.
- Finite presentation of F is `[SheafOfModules.IsFinitePresentation.{u} F]`.
  Its definition says locally cokernel of a map between finite free sheaves, precisely
  clause (2) of `def-weil-pbc-module-finite-type-presentation`.
  Nothing is assumed about G's finite type or presentation.
- The point is `(x : X)`.
- The internal Hom is the dependency's existing `SheafOfModules.homObj F G`, not a
  new internal-Hom construction. Its stalk is
  `↑(TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier)
  (SheafOfModules.homObj F G).val.presheaf x)`.
- The target is `F_x →ₗ[X.presheaf.stalk x] G_x`, with both module stalks given by
  Mathlib's abelian-group stalk and its existing module structure over the commutative
  stalk ring. These are exactly the carriers of the recorded stalk functors.
- “Is an isomorphism” is expressed by existence of a linear equivalence `e` between
  these O_X,x-modules. This is equivalent to a bijective linear canonical map.
- “Sending a germ of a local morphism to its induced stalk map” is the formula
  `e (germ Hom U x hxU φ) (germ F V x hxV s) =
  germ G V x hxV ((φ.app (op (Over.mk i))) s)` for every neighbourhood U,
  every local morphism φ, every smaller neighbourhood `i : V ⟶ U`, and every
  section `s : F.val.obj (op V)`. The section φ is definitionally a morphism of
  restricted module presheaves on `Over U`; evaluating its component gives the
  restricted morphism's action on sections. These are morphisms of sheaves because
  the restrictions are sheaves and the sheaf-module forgetful functor is fully faithful.
  This formula specifies the canonical map rather than an arbitrary abstract isomorphism:
  every Hom-stalk element is a representative germ, and every F-stalk element can be
  represented on a neighbourhood inside U by intersection. Thus the displayed formula
  determines e uniquely. It adds no hypothesis or independent conclusion.

Dependency declarations read and used:

- `def-weil-pbc-module-finite-type-presentation` is a Mathlib leaf. Its relevant
  declaration is `SheafOfModules.IsFinitePresentation`,
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`, line 267. Read the class,
  `QuasicoherentData.IsFinitePresentation`, `Presentation.IsFinite`, and the recorded
  explanation of the kernel/cokernel translation. This is the intended specialization
  to the open-set site, so no dependency module is needed.
- `def-pur-sheaf-hom`: `SheafOfModules.homObj`,
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`. Read its signature,
  docstring, underlying `PresheafOfModules.homObj` and `restrictOver` definitions in
  `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom`.
- `TopCat.Presheaf.stalk`, `TopCat.Presheaf.germ`, and the CommRingCat module-stalk
  instance in `Mathlib.Algebra.Category.ModuleCat.Stalk` supply the stalks and germs.
  The proof dependency `def-weil-pbc-module-stalk` was also read: its recorded
  `PresheafOfModules.moduleStalkFunctor` in `Sheaf.Topology.PresheafModuleStalkFunctor`
  wraps these same Mathlib carriers. No induced stalk morphism is needed as a separate
  declaration in this statement, because its action is specified directly on germs.

Edge cases checked before writing:

- Empty X: there is no x, so the assertion is vacuous, with no nonemptiness assumption.
- F = 0 (including a finite presentation with n = 0), or G = 0: both sides are zero
  modules and the canonical formula is still valid. No positive-rank assumption occurs.
- m = 0: finite locally free sources are included; no relations are required.
- No separation, characteristic, locality, or finite presentation of G is assumed.
- The germ formula permits V = U and arbitrary smaller neighbourhoods. It does not
  assume that all F_x elements are represented on one fixed U.
- All universes and variables are explicitly bound. A common arbitrary universe u
  accommodates the space, rings and modules; there is no independently smaller test
  universe. Explicit `C := Ab.{u}` avoids accidentally taking stalks in Type.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leanfinder`: “stalk of internal sheaf Hom of a finitely presented
  module is Hom of stalks”. Eight results: `ModuleCat.Tilde.toStalk`,
  `toStalk_comp_stalkToFiberLinearMap`, `stalkToFiberLinearMap`,
  `stalkToFiberLinearMap_toStalk`, `stalkIso_hom`,
  `toStalk_comp_stalkToFiberLinearMap_assoc`, `localizationToStalk`, `stalkIso`.
  These concern quasi-coherent sheaves on affine spectra, not internal Hom on a
  general ringed space.
- `msearch.py ... loogle`: `SheafOfModules.homObj, TopCat.Presheaf.stalk`.
  Zero hits; unknown identifier `SheafOfModules.homObj` (the declaration is in
  the source repository rather than the indexed Mathlib).
- `msearch.py ... leansearch`: “stalk of internal Hom sheaf of finitely presented
  modules is isomorphic to Hom of stalks”. Service unavailable: Internal Server Error.
  Recorded as unavailable; the other searches and direct source reads were used.
- `msearch.py ... grep`: `stalk.*[Hh]om|[Hh]om.*stalk` in
  Mathlib `Algebra/Category/ModuleCat`. Zero hits.
- `rg` of the item id in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`:
  zero hits. `tools/lean_names_upstream.py show` and reading the upstream-name record
  supplied no declaration for the item.
- `rg` of `stalk.*[Hh]om|[Hh]om.*stalk|internalHom|sheafHom` in project and source
  algebraic-geometry modules found existing stalk maps and internal Hom constructions,
  and the project `CoherentStalkMapExtends` citing this item as a proof input, but no
  statement of this isomorphism. The narrower algebra/module and topology searches
  found only existing stalk functors. A search of the proposed full declaration name
  in Mathlib, source, project and upstream names found no collision.

Source checked directly at https://stacks.math.columbia.edu/tag/01CP because the local
`literature/stacks-project/modules.tex` is absent on this machine. Its finitely presented
case and canonical germ formula agree with the node. No statement correction, missing
notion, unusable dependency, or disputed statement was found.

Validation: server compilation under the default timeout. The first compile required
explicit stalk categories/carrier coercions and an explicit finite-presentation universe;
these elaboration issues were fixed. A subsequent line-length warning was fixed by
wrapping the signature. The final compiler output and delivery dry run are recorded below.

## Second reading by P1

I independently read the item, both statement dependencies, their actual Lean
declarations, the stalk implementations, and all six proof steps. The local Stacks
checkout is absent. I read the source TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/modules.tex,
label `lemma-stalk-internal-hom`, and checked its tag at
https://stacks.math.columbia.edu/tag/01CP. The chapter introduction imposes no
additional finiteness, separation, or scheme assumptions. This item is precisely
the finitely presented case of 01CP, not its separate finite-type injectivity claim.

Object/hypothesis/conclusion checklist, in the node's order:

1. Ringed space `(X, O_X)`: `(X : RingedSpace.{u})` supplies the space and
   commutative ring sheaf `X.sheaf`. PASS: the source uses commutative ringed spaces;
   there is no locality, scheme, Noetherian, or separation requirement.
2. An O_X-module F: first binder of `F G : SheafOfModules.{u}` over the
   `sheafCompose` of `X.sheaf` with `forget₂ CommRingCat RingCat`. PASS: forgetting
   commutativity for the module category preserves the structure sheaf and its
   module notion, rather than changing the coefficient ring.
3. F finitely presented: `[SheafOfModules.IsFinitePresentation.{u} F]`.
   PASS: I read `Presentation`, `Presentation.IsFinite`, `QuasicoherentData`,
   `QuasicoherentData.IsFinitePresentation`, and `IsFinitePresentation` in Mathlib's
   `Sheaf/Quasicoherent.lean`. A cover with finite generators and finite relations
   is exactly local finite free cokernel presentations. The two directions are
   exhibited by `presentationOfIsCokernelFree` and `Presentation.isColimit`.
   This is the relevant clause (2) of the recorded Mathlib dependency, not merely
   finite type or quasi-coherence. No unusable dependency needs replacement.
4. An arbitrary O_X-module G: second binder of `F G`. PASS: there is no class
   hypothesis on G.
5. Point x of X: `(x : X)`. PASS: every point, with no closed/generic assumption.
6. Internal sheaf Hom: `SheafOfModules.homObj F G`. PASS: the recorded dependency
   in `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom` uses
   `PresheafOfModules.homObj` for its data and the existing named sheaf theorem
   for its sheaf structure. I read `restrictOver` and the underlying `homObj`:
   its U-sections are morphisms on `Over U`, with restriction along inclusions
   and the required O_X(U)-action. These are the sheaf morphisms of the node,
   via the fully faithful forgetful functor, not just maps of global sections.
7. Source stalk Hom(F,G)_x: the carrier of
   `TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier)` applied to the Hom
   module's underlying presheaf. PASS: an abelian-group stalk with Mathlib's
   induced module structure, not a stalk in Type with forgotten operations.
8. Target Hom over O_X,x: the displayed linear-map type between the F and G
   abelian-group stalks, with scalars `X.presheaf.stalk x`. PASS: I read both
   stalk-module instances and `germ_smul` in `ModuleCat/Stalk.lean` and the
   project's presheaf and ringed-space stalk functors. Their object carriers
   are these same Mathlib stalks; no second stalk construction is introduced.
9. The canonical germ-to-stalk-map rule: for every U containing x, every local
   morphism phi, every V with `i : V ⟶ U` and x in V, and every section s on V,
   the final equality says `e (germ phi) (germ s) = germ (phi_V s)`.
   PASS: `phi.app (op (Over.mk i))` is exactly its component on V.
   Every source stalk element has such a representative, and every F-stalk
   element can be restricted to a neighbourhood inside U using intersection.
   Thus the equality specifies the canonical map on all arguments, not an
   arbitrary isomorphism. The binders are after the single existential e, so
   the same map works for every representative and neighbourhood.
10. Isomorphism: `∃ e : ... ≃ₗ[X.presheaf.stalk x] ...` with that rule.
    PASS: a bijective linear canonical map is equivalent to this linear
    equivalence. The germ equation is its specification, not an added
    independent conclusion or hypothesis.

Edge cases: empty X has no x and the assertion is vacuous, as in the source;
zero F and zero G are permitted. The finite-presentation class allows empty
generator and relation types (n = 0 and m = 0), including the zero module and
finite free modules. No positive rank, nontrivial stalk ring, characteristic,
or nonempty index-set condition occurs. U and V must contain the already
chosen point, as required for germs; V may equal U. The sole universe u is
arbitrary, and all space/ring/module data can be lifted into a common universe;
there is no smaller independent test universe or unbound variable.

Independent H4 searches (2026-10-11):

- LeanFinder through `msearch.py`: "For a finitely presented sheaf on a ringed
  space every linear map of stalks extends locally uniquely as a germ".
  Eight hits: the Tilde germ/stalk-to-fibre maps and `stalk_hom_ext` /
  `stalk_hom_ext_iff`. These concern affine associated modules or extensionality
  of maps out of an individual stalk, not the present Hom-stalk isomorphism.
- Loogle through `msearch.py`: `TopCat.Presheaf.stalk, LinearEquiv`.
  One hit, `StructureSheaf.commRingCatStalkEquivModuleStalk`, compares two
  encodings of the structure-sheaf stalk on Spec R and is not this statement.
- Grep through `msearch.py`: `finite.*[Pp]resent.*[Hh]om|[Hh]om.*finite.*[Pp]resent`;
  direct rg also searched stalk/Hom/equivalence combinations in Mathlib's
  ModuleCat, the source's ModuleCat, and the project's algebraic geometry,
  and finite-presentation phrases in source ModuleCat and Mathlib sheaves.
  I additionally searched `homObj|internal.Hom` in project topology and read
  `CoherentStalkMapExtends`: that narrower extension theorem cites this node
  as a proof input and does not replace it. None supplies the present theorem.
- Searching the proposed declaration name and blueprint id in source Lean and
  the upstream-name record found no collision or existing implementation.

There are no new definition nodes, dependency modules, or statement correction
in this delivery. H5/H6: the module has no definitions and exactly one named
theorem with `sorry`; nothing is proved. H8: its source and blueprint docstrings
are present, and its six proof paragraphs match all six node steps, including
the common-kernel comparison. H9: imports serve the ringed space, stalk/module
structure, finite-presentation class, and existing internal Hom; the namespace,
header, explicit universe, and line lengths meet the conventions.

No mathematical or Lean mismatch was found, so I left the module and node
unchanged. The stored `lean.statement` equals the file's signature verbatim.
The only change is this independently written second-reading report.
Compilation with `scompile.py` from the sandbox succeeded in 3.8 seconds,
exit code 0, with no warnings or errors.
