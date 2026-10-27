## Worker report

The delivery states `AlgebraicGeometry.relativeDualizingPair_open_rigidity` and
`AlgebraicGeometry.relativeDualizingPair_open_base_iff` in
`Sheaf.AlgebraicGeometry.RelativeDualizingPairOpenRigidity`. It preserves the accepted
stage-1 split and its natural-language statement. The earlier worker's stage-1 refusal
does not apply: coord/brief-stage2.md §0 explicitly authorizes this stage-2 handoff.
This packet repairs the H2 return on immutable head `aa0a35124c08`.

The module supplies real canonical transport definitions needed to state the open
clauses, all in the owning node's module. The only postponed proofs are the two
statement clauses above and `relativeDualizingOpenDiagonalMap_isIso`, the invertibility
of the diagonal identification in proof steps 1 and 5. In particular the inverse in
`relativeDualizingOpenClass` is the inverse of a specified actual morphism, uniquely
determined by invertibility, rather than an arbitrary identification or class.

Hypotheses and clauses, matched individually:

- Arbitrary schemes and their specified map: `{X S : Scheme.{u}} (f : X ⟶ S)`.
  `u` and the derived morphism universe `w` are explicit and independent.
- Separated, flat and locally finitely presented: `[IsSeparated f] [Flat f]
  [LocallyOfFinitePresentation f]`. No Noetherian, quasi-compactness, nonempty,
  finite-cover, affine or proper hypothesis is present. The proper-morphism node
  supplies `IsSeparated`, not an assumption `IsProper`.
- The two supplied objects and classes: `K L : schemeDerivedCategory X`, and
  `ξ`, `η` have source `DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f)`
  and targets `(derivedPullback (pullback.fst f f)).obj K` and the analogous L.
  `hK`, `hL` assert precisely `IsCoherentRelativeDualizingPair` for these supplied data.
- The diagonal and first projection are the library's `pullback.diagonal f` and
  `pullback.fst f f`, with the existing ordinary diagonal algebra and degree-zero
  complex. No replacement relative-dualizing predicate is introduced.
- The scalar map is an isomorphism: `IsIso (relativeDualizingScalarMap X K)`.
  The definition is exactly the canonical transpose of the unit action with target
  the library's `derivedInternalHom` of `(K,K)`; the domain is the derived tensor
  unit, namely the structure sheaf in degree zero.
- Exactly one class-preserving isomorphism globally: the separate conjunct
  `∃! α : K ≅ L, ξ ≫ (derivedPullback (pullback.fst f f)).map α.hom = η`.
  This quantifies over isomorphisms of the derived objects, and is not merely
  uniqueness of cohomology maps or of choices with additional restrictions.
- Every open source restriction: the theorem quantifies over schemes X', S', maps
  `j : X' ⟶ X`, `b : S' ⟶ S` with `[IsOpenImmersion j] [IsOpenImmersion b]`, and
  `h : f' ≫ b = j ≫ f`. Set X' = U.toScheme, j = U.ι, S' = S,
  b = 𝟙 S and f' = U.ι ≫ f to obtain exactly every open U in the statement.
  The properties of f' are explicitly typed instances; they are consequences of
  those of f for these open squares, so no open is excluded. This also presents
  the source and base restrictions simultaneously, including their composites.
- Actual restrictions of BOTH supplied pairs: two conjuncts of
  `IsCoherentRelativeDualizingPair f'` with object
  `(relativeDualizingOpenRestriction j).mapDerivedCategory.obj K` (respectively L)
  and class `relativeDualizingOpenClass ... K ξ` (respectively L η).
  The restriction abbreviation is just Mathlib's `Scheme.Modules.restrictFunctor`
  typed on the shared `SheafOfModules` categories. Its instances are reuses of
  the existing exact-functor instances, not new mathematical hypotheses.
- The restricted scalar assertion is
  `IsIso (relativeDualizingScalarMap X' (...obj K))`.
- Restricted rigidity is a separate `∃! β` between the two restricted derived
  objects, satisfying precisely the restricted class-preservation equation.
- Compatibility of comparisons is the final universal clause: every global α
  preserving ξ restricts by `.mapDerivedCategory.map α.hom` to a map preserving
  the two canonical restricted classes. Together with restricted uniqueness,
  this identifies the restricted comparison with the comparison constructed there.
- Empty opens are included: there is no Nonempty condition anywhere. Take
  U = ⊥ in the preceding instantiation. The diagonal identification and classes
  are also defined for that open, and the theorem asserts the same conclusions.
- An open V in S through which f factors is rendered explicitly by
  `(V : S.Opens) (g : X ⟶ V.toScheme)` and `h : g ≫ V.ι = (𝟙 X) ≫ f`.
  `relativeDualizingPair_open_base_iff` states an IFF between the original and
  transported supplied-pair predicates for arbitrary supplied K and ξ, without
  assuming either predicate. It also states, for EVERY isomorphism α, an IFF
  between the two class-preservation equations. Apply the predicate clause with
  K replaced by L for the second pair. The scalar map itself is intrinsic to X
  and has no base parameter. Thus this is the same pairs and comparisons for X/V,
  with the identity restriction on X retaining its canonical unit identification.

The canonical transports are fully specified:

1. `relativeDualizingOpenSquare` is the ordinary `pullback.map` on the two open
   inclusions and their commutative squares.
2. `relativeDualizingOpenPullbackIso` compares the pinned derived pullback
   adjunction (`relativeMVAdj`) with the derived adjunction of ordinary exact
   sectionwise restriction, using uniqueness of left adjoints. It has no freely
   supplied natural isomorphism.
3. `relativeDualizingOpenDiagonalModuleMap` is the adjunction-normalized
   identification from restriction to tensor pullback, followed by the EXISTING
   module base-change map for the square of diagonals and the pushforward of
   `tensorPullbackObjUnitToUnit j`. Thus its normalization is the map on actual
   sections and preserves the unit, rather than a freely chosen algebra map.
4. `relativeDualizingOpenDiagonalMap` is its degree-zero localization, using
   `singleFunctorIsoCompQ` and `mapDerivedCategorySingleFunctor`. Its named
   invertibility theorem is exactly the canonical diagonal restriction
   identification used by proof steps 1 and 5; its docstring gives that proof.
5. `relativeDualizingOpenFirstProjectionIso` uses the EXISTING pinned
   `relativeMVComp` comparisons, their equality transport, and the preceding
   open adjunction comparisons.
6. `relativeDualizingOpenClass` is the inverse canonical diagonal map, then the
   exact restriction of the original supplied ξ, then the first-projection
   comparison. It does not quantify over a replacement ξ or choose class data
   from an existence assertion.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- WeilConjectures.AlgebraicGeometry.DerivedCategory:
  `AlgebraicGeometry.schemeDerivedCategory`.
- WeilConjectures.AlgebraicGeometry.DerivedPullback: `derivedPullback`, with its
  shared localization instances, canonical counit and K-flat characterization.
- Mathlib.AlgebraicGeometry.Morphisms.Proper (via Separated): `IsSeparated`.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `Flat` (equivalent to flat stalk maps).
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  `LocallyOfFinitePresentation` and `finitePresentation_appLE`.
- Sheaf.AlgebraicGeometry.RelativeDualizingPair: the recorded
  `IsCoherentRelativeDualizingPair`, `relativeDualizingDiagonalModule`,
  `relativeDualizingDiagonalComplex`, `relativeDualizingScalarMap` and their
  canonical class/tensor-Hom construction.
- Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom: the recorded module
  publicly preserves the generic ringed-site construction through
  DerivedInternalHomOfUniverses; ordinary ModuleCat RHom is not applied to sheaves.
  The scalar-map interface uses `CategoryTheory.derivedInternalHom`, read in
  WeilConjectures.Algebra.Homology.DerivedInternalHom, already publicly supplied
  by the coherent-pair module and its canonical tensor-Hom dependencies.
- WeilConjectures.AlgebraicGeometry.RelativeMVMaps:
  `relativeMVAdj`, `relativeMVComp`. Added its already landed owner
  `def-pc-relative-mv-maps` to stmt_deps.
- WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction:
  `Scheme.Modules.moduleBaseChangeMap`. Its landed definition owner
  `def-sfb-module-base-change-map` is in stmt_deps. The open-restriction theorem
  is not required to define this map.
- WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf:
  `Scheme.Modules.tensorPullbackObjUnitToUnit`. Added the already landed
  `def-sfb-tensor-pullback-structure-sheaf-map` to stmt_deps.
- The remaining public imports expose the existing exact restriction instances
  and `Adjunction.mapDerivedCategoryRightDerivedAdjunction`.
- All currently recorded proof dependencies are imported privately:
  AffineDerivedPullbackTensorTilde, CanonicalPullbackTensorComparison,
  OpenRestrictionEvaluationMateIsIso, CanonicalDerivedTensorHom and
  RingedSiteRestrictionKFlat. The finite-presentation leaf is already public.
  The four proof nodes arbitrary-base-affine-dualizing-realization,
  arbitrary-ring-relative-dualizing-homothety,
  arbitrary-ring-relative-dualizing-isomorphism and
  trf-diagonal-class-basis-descent have no recorded Lean module on the read base;
  they remain cited in proof_deps and by name in the complete proof docstring.
  None is needed to type this statement, and none is silently replaced with a
  Noetherian specialization.

Sources and edge cases: read duality.tex at lemma-relative-dualizing-RHom,
lemma-uniqueness-relative-dualizing and lemma-existence-relative-dualizing, including
its open-restriction parenthesis and the V-perfect/S-perfect and fibre-square
identifications. The source has no Noetherian assumption. Checked the empty open,
empty base (forcing empty source), identity source restriction, identity base
restriction, arbitrary non-quasi-compact opens and arbitrary non-Noetherian bases.
For the identity base the fibre-square map is restriction to U ×_S U; for the
identity source and open base it is the canonical identification X ×_V X ≅ X ×_S X.
No object data are sorry, and the only chosen maps come from uniqueness of the
specified adjunction comparisons or the inverse of the specified canonical map.
No statement correction, new independent definition node or dependency repair is needed.

Searches (the msearch calls are recorded in searches.jsonl in the sandbox):

- msearch leanfinder: "Relative dualizing pairs for flat locally finitely presented
  schemes restrict to opens and have unique diagonal-class-preserving isomorphisms".
  Eight hits: diagonalRestrictIsoDiagonal, Flat.instMorphismRestrict,
  Flat.instResLE, arrowResLEAppIso, Flat.flat_appLE,
  morphismRestrictRestrictBasicOpen, fst_inv_eq_snd_inv and
  morphismRestrictOpensRange. None states relative-dualizing rigidity.
- msearch loogle: "IsCoherentRelativeDualizingPair, relativeDualizingScalarMap".
  Zero hits; the project-specific identifier is not in the Mathlib Loogle index.
- msearch grep: "relativeDualizing|RelativeDualizing". Zero Mathlib hits.
- rg of the same notions in lean/WeilConjectures: no pre-existing relative-pair
  rigidity declaration. rg of the item id in WeilConjectures and the upstream
  name index found no attachment.
- rg of lean/Sheaf located RelativeDualizingPair.lean, its NOETHERIAN sibling
  RelativeDualizingPairRigidity.lean, AffineRelativeDualizingComparison.lean,
  RelativeDualityPolynomialChart.lean and related polynomial restriction files.
  Read the sibling's full two signatures and docstrings: both impose
  `[IsLocallyNoetherian S]`, so neither states this arbitrary-base node.
- Searched the canonical maps and open restriction APIs, locating and reusing
  RelativeMVMaps, ModuleBaseChangeMapOpenRestriction, TensorPullbackStructureSheaf,
  Scheme.Modules.restrictFunctor, and their shared derived-category transports.

Validation: every compile uses scompile.py only, on the live server, with the
standard limit. Earlier elaboration errors were repaired by exposing the exact
restriction functor on the shared sheaf-module categories, retaining independent
universe w, and stating invertibility of the actual diagonal map before using its
uniquely determined inverse. Final compile and dry-run results are recorded below.

Final validation: scompile.py checked both the sandbox and the named library module
cleanly (38.8 s and 31.3 s). deliver2.py --no-push then returned
`OK (dry run): commit 169c4a81d5e passes the preflight and compiles; nothing pushed`.


## Repair of H2 return

Replaced `lem-weil-pbc-module-base-change-map-open-restriction` in stmt_deps with
`def-sfb-module-base-change-map`, exactly as requested by the maintainer. Q51's
node is now landed in the shared DAG, with `existing: true`, module
`WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`, declaration
`AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap`, and statement dependencies
`def-pc-scheme` and `lem-pc-module-pullback-adjunction`. No copy is needed in this
packet. Read its full node and the definition's docstring, signature and body:
the map is the canonical adjunction mate using pushforward composition and the
pullback unit. This is precisely the ordinary map used by
`relativeDualizingOpenDiagonalModuleMap`; no conclusion of the open-restriction
theorem is used to define it. Invertibility remains separately stated by
`relativeDualizingOpenDiagonalMap_isIso`.

The Lean file and signature are unchanged from the returned packet. Comparing
with current main shows only the authorized stmt_deps additions and the lean
record; the natural-language statement, proof and proof_deps are unchanged.
The initial saved-packet dry run passed at `ac4ac9d11ed`; that result preceded
this required repair. Validation of the repaired packet follows below.


## Second reading by NO

Author's repair self-check; the maintainer supplies the independent reading.
Read the node, module and landed definition owner together. Separated, flat and
locally finitely presented hypotheses, the two supplied classes, the scalar
isomorphism, unique class-preserving comparison, all open restrictions and the
open-base equivalence retain exactly their reviewed signatures. In particular
there is no Noetherian hypothesis, nonempty-open condition or universe equality.
The sole returned defect is repaired by citing the definition owner for the plain
module base-change map. The dependency replacement changes no Lean term. Checked
that lean.statement remains verbatim and that only lean and stmt_deps differ from
current main. No new nodes or dependency modules are included.

Repair compile: scompile.py passed with no errors or unexpected warnings, checking
the sandbox module in 38.8 s and its library-named form in 31.3 s.
