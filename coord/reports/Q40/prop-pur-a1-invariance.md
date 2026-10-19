## Worker report

The delivery states `WeilConjectures.affineLine_invariance` in
`lean/Sheaf/Paper/AffineLineInvariance.lean`. Its only postponed theorem is the item
itself, with proof `sorry`. The docstring gives the node's complete proof route:
finite coefficients, absorption of local twists, finite clopen shift partition,
componentwise exact reconstruction, reduction to sheaves, the two lisse uniqueness
assertions, ordinary sheaf-map gluing, normalization, and the two fibre comparisons.
All helpers have real definitions and are listed in `lean.declarations`.

I read the complete target node and its statement dependencies, their available
records and declaration sources, the source blueprint proposition and its unit,
and the upstream affine-line module. The shared checkout does not contain regenerated
literature; the blueprint was read in the existing read-only `work-bp/sheaf/literature`
copy. The statement agrees with the current DAG and the source. No statement
correction or disputed statement is proposed.

### Hypotheses and their Lean counterparts

- The fixed setting is `P : PurityFiniteSetting`. It retains the global finite-field
  datum, the prime ell distinct from its characteristic, fixed coefficient closure,
  finite subextension E, and positive quotient level. `P.Ring` is precisely the
  published `Padic.coefficientExtensionRing` at that level. `P.Coefficient` is its
  standard size lift, not an independently supplied coefficient ring.
- The finite-coefficient interpretation is the one explicitly prescribed in
  `def-pur-conventions`: the assertions here are made for A, and integral/rational
  versions are later coefficient transports. No integral or rational category is
  identified with ordinary finite sheaves.
- `Y.Over (Spec (.of P.field.k))` is the k-scheme structure. The `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact` instances on its structure morphism
  express separated and finite type, including quasi-compactness.
- The affine line is `AffineSpace (ULift (Fin 1)) Y`; its projection is `↘ Y`.
  The sections are the published `AffineSpace.zeroSection` and `oneSection`.
  Their defining retraction equations are the existing `*_comp_over` lemmas.
- `F` and `C` are ambient derived objects, with `hF : P.a1Ctf _ F` and
  `hC : P.a1Ctf Y C`. `a1Ctf` applies the recorded `finiteTorConstructible`
  predicate after the canonical exact intrinsic realization. Thus these are exactly
  objects of the full Dctf subcategories, and Hom and Iso are their ambient Hom and
  Iso, as appropriate for a full subcategory.
- `a1Category` is `DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat P.Coefficient))`.
  `finiteCoefficientIntrinsicRealization` identifies this with the ringed-site
  presentation used by the recorded Dctf predicate. Both use the actual small
  pro-etale site with object universe u+1 and morphism universe u; no equality of
  these universes is imposed.
- `θ` is exactly the isomorphism from the pullback of F along t=1 to C.
- `I : Type v`, `U`, and `u` are the covering family. Every `u α` is `Etale`.
  The three properties on `u α ≫ Y ↘ Spec k` state that each covering scheme is
  separated and finite type over k. `hcover` is joint surjectivity on points;
  for an etale family this is precisely the small-etale covering condition.
  The index universe is arbitrary: no nonempty, finite, affine, or connected
  cover assumption is added.
- `hshape` states for each α the existence of a sheaf L and integers m,n with
  `P.a1RankOne _ L` and an isomorphism between the restricted F and
  `singleFunctor 0` of `P.a1TwistedSheaf _ L m`, shifted by n. The integers
  are independently quantified for every α.
- `a1RankOne` uses the dependency's
  `IsLocallyConstantProEtaleFixedModuleSheaf` and the published
  `SheafOfModules.IsFiniteLocallyFreeOfRank ... 1` on its canonical intrinsic
  realization. These are coverwise module conditions, not an arbitrary stalkwise
  label. Over the actual finite coefficient ring the rank-one trivializations
  also give finiteness of the local stalks.
- `a1TateLine` specializes the already published `finiteEtaleTateSheaf` to A and
  its characteristic N, then uses `comparisonUpperStar`. This is the usual
  finite torsion construction A tensor over Z/N with mu_N. Here N is an ell-power
  killing A; it is invertible on every k-scheme in the fixed setting. It gives
  exactly the reduction of the inverse-limit Tate line of
  `def-coefficient-twists-detailed`: projection of the compatible roots to mu_N,
  followed by tensor with A, gives the canonical identification. Positive twists
  use tensor powers, zero the coefficient unit, and negative twists the sheaf
  dual, as in the dependency. This uses a canonical annihilator, without the
  ramification-divides-level restriction of the older `P.twist` interface.
  `a1TwistedSheaf` tensors L with this line using the published sheaf monoidal
  structure. Since the twisting line is locally free of rank one, it is flat;
  this ordinary sheaf tensor placed in degree zero computes the source's derived
  twist of L. No arbitrary twist datum or choice of a primitive root is used.
- `κloc` is exactly the family of isomorphisms from restricted F to the restriction
  of a-star C. The node uses the latter form, so no extra base-change isomorphism
  on the projection is needed in its codomain.
- `hnormal` is the normalization equation. Its left side is i1-star of `κloc α`,
  followed by the canonical base-change square at t=1 and by u-star of
  i1-star a-star C = C. Its right side is that same square on F followed by
  u-star θ. `a1OneBaseChange` constructs the square from composition and equality
  comparisons of the actual published pullbacks, verifying the affine coordinate
  with `homOfVector_comp_map` and `comp_homOfVector`. These comparisons are
  constructed maps, not extra hypotheses.

### Conclusions and their Lean counterparts

The conclusion has one `∃ κ : F ≅ a* C`, followed by all the following conditions.

1. Its first conjunct says that every affine-line restriction of κ equals the
   prescribed `κloc α`. The next conjunct quantifies over every other isomorphism
   with those restrictions and asserts `κ' = κ`. These give clause (1), existence
   and uniqueness for the supplied local comparisons.
2. The next conjunct is `a1FibreComparison ... oneSection ... = θ`. The next
   quantifies over every other isomorphism with that normalization, regardless
   of its local restrictions, and asserts `κ' = κ`. These are clause (2), and
   also imply independence from both the covering family and its comparisons.
3. The final conjunct supplies an isomorphism e between the zero and one fibres
   and specifies it to be `a1FibreComparison ... zeroSection ... ≪≫ θ.symm`.
   `a1FibreComparison` is i_s-star κ composed with the actual canonical section
   comparison to C. Thus this is exactly the source's displayed chain, with
   its right-hand comparison θ, not just an unspecified `Nonempty` isomorphism.
   The preceding uniqueness of κ makes this specified chain canonical.

### Dependency declarations and interfaces

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, its
  `Ring` and `Coefficient`, their instances, and the published finite-field data.
- `Mathlib.AlgebraicGeometry.AffineSpace` and
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`,
  `AffineSpace.map`, `zeroSection`, `oneSection`, and their section equations.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
  and `.Iso`: `AlgebraicGeometry.ProEtale.upperStar`, `upperStarComp`,
  `upperStarId`, and `upperStarCongr`. The finite clause of
  `def-weil-derived-pullback-tensor-hom` is exactly this exact inverse image
  descended termwise by `Functor.mapDerivedCategory`; it needs no new
  finite-level derived-pullback definition or unstated datum. The helpers
  retain its actual canonical composition and identity maps.
- `Sheaf.Paper.ProEtaleFixedModuleLocalConstancy`:
  `AlgebraicGeometry.Scheme.IsLocallyConstantProEtaleFixedModuleSheaf`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`.
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`:
  `AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization` and its
  published exactness instances. The already landed node
  `def-weil-pbc-proetale-modules` is added to statement dependencies for this
  coefficient-presentation transport.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf`:
  `AlgebraicGeometry.Scheme.finiteEtaleTateSheaf`, reexported by the purity
  setting. The already landed `def-asd-finite-etale-tate-sheaf` is added to
  statement dependencies. The finite roots construction supplies the exact
  finite-level twist used here even though the omnibus coefficient-twist
  node has no Lean record yet; the unused integral and rational constructions
  are not redefined by this delivery.

The remaining recorded proof modules are imported without `public`. Two proof-only
imports cannot coexist with this module's finite-coefficient framework:
`Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives` imports the older
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Injective`, and
`Sheaf.AlgebraicGeometry.ProEtaleStalkConservative` imports the older
`...LowerShriek.OpenImmersion.Defs`. Both reach the older
`...ProEtale.UpperLowerStar.Defs`, which duplicates the declarations in the
published `...ProEtale.FiniteCoefficient.UpperLowerStar.Defs`. A compile with
both records failed with `environment already contains` on the pro-etale
pushforward notation. Following the launcher's duplicate-import repair rule,
these two imports are omitted, and the compatible
`...FiniteCoefficient.LowerShriek.Open.Defs` supplies the underlying restriction
construction. Their DAG proof dependencies and mathematical uses remain in the
proof docstring. Their older wrappers need compatible imports before stage 3
can directly import those additional statements here; this is not a change to
any statement or any live source file.

### Edge cases

Checked the empty scheme: an empty etale cover is allowed by `hcover` exactly
when Y is empty, and its derived module category has singleton Hom sets, so both
uniqueness assertions and the specified fibre map are appropriate. No `Nonempty I`
hypothesis is imposed. Empty members of a nonempty cover are harmless. A zero F or
C over a nonempty covered base cannot satisfy the rank-one local shape and the
normalized comparison, because the actual positive coefficient quotient is
nonzero. Thus no accidental zero-object counterexample is hidden. Disconnected
bases and differing local shifts are permitted; the proof partitions by the shift
instead of assuming one global integer. Twist m=0, positive m, negative m, and
shift n=0 are included. There is no restriction on the quotient level beyond its
existing positivity, in particular no divisibility by the ramification index.
The finite-type condition includes quasi-compactness. Neither F nor C is required
to be globally lisse, concentrated in one degree, or supplied with an etale origin.

### Searches and reuse

Actual searches used the prescribed `msearch.py Q40 prop-pur-a1-invariance` wrapper:

- LeanFinder, `derived category affine line invariance gluing unique isomorphism`:
  eight unrelated/general hits, including the general single-degree concentration
  theorem; none states this gluing and normalized uniqueness proposition.
- Loogle, `DerivedCategory, IsIso, AffineSpace`: zero hits; the service reported
  `unknown identifier 'IsIso'`. A second query, `AlgebraicGeometry.AffineSpace`,
  returned the affine-space construction, projection, and map, which are reused.
- LeanSearch, `Isomorphisms of locally constant sheaves over affine line glue uniquely
  normalized at one section`: service unavailable (Internal Server Error). This is
  reported as unavailable, not as evidence of absence.
- Mathlib grep through the wrapper, `A1|a1|AffineSpace` in the initially supplied
  Mathlib/AlgebraicGeometry subdirectory, and `oneSection|a1_invariance|a1Invariance|
  affineLine.*[Ii]nvar` in AlgebraicGeometry: no exact theorem. The successful
  Loogle result and direct source reading located the affine-space API.
- LeanFinder, `finite torsion Tate twist roots of unity module sheaf`: eight hits
  about ordinary roots of unity in rings/number fields, none for this sheaf twist.
- Direct `rg` of Mathlib, upstream `WeilConjectures`, and `lean/Sheaf` for the
  proposed full names found no duplicate helper or theorem declaration.
  Direct `grep -rn prop-pur-a1-invariance` of upstream found no exact attachment.
- Read upstream `EtaleCohomology/Purity/Smooth/AffineLine.lean`, especially its
  implementation note and `eq_of_leftDerivedUpperStar_oneSection_eq`. It explicitly
  says that only uniqueness, not gluing, is stated. It also uses the etale derived
  category. It therefore cannot replace this proposition.
- Queried current sources with `scompile.py --source` for the unrecorded omnibus
  `Sheaf.Paper.DerivedPullbackTensorHom`, `Sheaf.Paper.CoefficientTwistsDetailed`,
  and `Sheaf.Paper.TwistSheafLocallyFree`: unavailable. Existing draft deliveries
  were inspected read-only; none was assumed landed or imported. All objects needed
  for this finite-level item are supplied by the published declarations named above.

### Validation

The statement with its explicit twist and all three conclusion clauses passed
`scompile.py` without errors or warnings. After checking the recorded proof imports,
the two incompatible older imports described above were removed. The final module
and required delivery dry run are checked again before answering READY.

## Second reading by Q40

I independently read the sandbox node and the whole delivered module, then the
blueprint proposition and its enclosing unit `sk-prop-a1-inv` in the available
literature checkout. The proposition's source is this blueprint, rather than a
Stacks theorem. I also read the chapter's `def-pur-conventions` source and the
Stacks Kummer section (Tag 03PK, `section-kummer`), including its invertibility
hypothesis. The source proposition and the current DAG statement agree. There is
no statement correction and no new node or dependency module in this delivery.

The object/hypothesis/conclusion checklist, in source order, is as follows. Each
entry passes.

1. Fixed purity setting: `P : PurityFiniteSetting.{u}`. I opened the published
   `PurityFiniteSetting`, `FiniteFieldDatum`, and `CoefficientDatum` declarations:
   they retain p, a, q, the finite field and fixed algebraic closure k, ell prime
   different from p, the fixed coefficient closure, its actual finite subextension
   E, and a positive quotient level. `P.Ring` is the recorded quotient, and
   `P.Coefficient` is its ULift. The source explicitly makes the assertions at
   finite coefficients A; using this setting does not omit an integral assertion.
2. Separated finite-type k-scheme Y: `Y : Scheme.{u}`, `Y.Over (Spec (.of
   P.field.k))`, and the `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`
   instances on its structure morphism. Finite type includes quasi-compactness;
   no smoothness, connectedness, or nonemptiness hypothesis has been added.
3. Affine line, projection and sections: `AffineSpace (ULift.{u} (Fin 1)) Y`,
   its canonical `↘ Y`, and the published `AffineSpace.zeroSection` and
   `oneSection`. I opened Mathlib's pullback construction of `AffineSpace`, its
   `over` instance, and the upstream definitions and section equations. The
   one-element coordinate type gives precisely relative dimension one.
4. Objects F and C in Dctf: the two ambient `P.a1Category` binders and `hF`,
   `hC : P.a1Ctf ...`. I read `finiteTorConstructible` (the finite declaration,
   not the dependency record's primary integral declaration), which is bounded
   constructibility intersected with finite Tor amplitude. `a1Ctf` applies it
   after `finiteCoefficientIntrinsicRealization.mapDerivedCategory`. I opened
   this actual realization: it sheafifies the given module presheaf along the
   constant-scalar unit, and its published exactness theorem identifies the two
   presentations. Thus these are ambient objects with exactly the full
   subcategory's membership conditions; ambient Hom and Iso are appropriate.
5. The specified theta: `θ : (P.a1Pullback oneSection).obj F ≅ C` is an
   isomorphism with the source's domain and codomain. I read the finite-coefficient
   `ProEtale.upperStar` construction and its exactness interface; the
   `mapDerivedCategory` here is the source's exact inverse image applied termwise.
6. Cover: `{I : Type v}`, `U : I → Scheme.{u}`, maps `u`, their `Etale`
   instances, and `hcover` give an arbitrary jointly surjective etale family.
   The three instances on each `u α ≫ Y ↘ Spec k` say that its member is
   separated finite type over k, with the induced k-structure. They do not
   demand that a member be affine or that the cover be finite.
7. Local shape: `hshape` independently quantifies `L`, `m n : ℤ` for every
   member, requires `P.a1RankOne _ L`, and supplies an isomorphism to
   `singleFunctor 0` of `P.a1TwistedSheaf _ L m`, shifted by n. I opened
   `IsLocallyConstantProEtaleFixedModuleSheaf`: it is an actual covering and
   local isomorphisms to sheafified constant modules, without a hidden finite
   condition. I opened `SheafOfModules.IsFiniteLocallyFreeOfRank`: it requires
   local free generators indexed by `Fin r`. Its specialization to r=1 on the
   canonical intrinsic realization supplies the rank condition. Since A is the
   actual finite quotient, local free rank one also supplies the stated finite
   local module. Neither notion is a bare stalkwise replacement.
8. Integer twists in that shape: `a1TateLine` specializes the existing
   `finiteEtaleTateSheaf` to `ringChar P.Coefficient` and applies the comparison
   inverse image. I opened `finiteEtaleTateSheaf`, `finiteEtaleTateTwist` and
   `finiteEtaleTateLine`: these are scalar-extended roots of unity in degree one,
   the constant module in degree zero, tensor powers in positive degrees and
   sheaf Hom duals in negative degrees. For this nonzero quotient its
   characteristic is an ell-power, hence invertible on every k-scheme here.
   Projection of compatible ell-power roots to that annihilator identifies this
   finite Tate line with the reduction in `def-coefficient-twists-detailed`.
   This construction works at every positive quotient level, including those
   not divisible by the ramification index. Tensoring by this locally free
   line computes the derived twist of L. It is the canonical finite-level
   specialization, without a freely supplied twist or a trivialization choice.
9. Local comparisons: `κloc α` has exactly the restricted F and restricted
   a-star C as its two objects. It is supplied as data, before the conclusion,
   so gluing concerns the given comparisons rather than newly selected ones.
10. Local normalization: `hnormal` pulls `κloc α` back along the unit section,
    uses `a1OneBaseChange` to change the order of the two pullbacks, and then
    applies u-star to `a1SectionComparison`. The other side is the same square
    on F followed by u-star theta. I checked both orientations by expanding
    `a1PullbackComp`, `upperStarCongr`, `upperStarId`, and the derived functor
    comparisons. The coordinate calculation in `a1OneBaseChange` proves the
    actual square `oneSection ≫ map u = u ≫ oneSection`; it is not an assumed
    comparison. Thus the equation is precisely the source's normalization.
11. Gluing conclusion: `∃ κ : F ≅ a* C`, its first conjunct of equal local
    restrictions, and its second conjunct quantifying every other such κ'
    give exactly existence and uniqueness for the supplied local data.
12. Normalized uniqueness: the next equality is
    `a1FibreComparison ... oneSection ... = θ`. The following universal
    implication asserts equality of every other normalized isomorphism with κ,
    even if it is not given to match the local data. This is exactly clause (2)
    and implies the source's independence from the cover and comparisons.
13. Two fibres: the final existential gives an actual isomorphism e from the
    zero fibre to the one fibre and fixes it to the zero-section comparison
    followed by `θ.symm`. The right-hand comparison is theta by entry 12.
    This is exactly the displayed chain in clause (3), with its prescribed
    maps; it is not just an unspecified existence of isomorphic fibres.

Edge cases checked: an empty index type is allowed precisely when `hcover`
forces Y empty. Empty cover members cause no restriction. On the empty scheme
rank-one local conditions and the conclusion are interpreted in the zero sheaf
category, and both uniqueness assertions remain correct. Over a nonempty base,
zero F or zero C cannot satisfy the local rank-one shape and normalized
comparisons, since the positive coefficient quotient is nonzero. Disconnected
bases, different local shifts, n=0, negative shifts, m=0, positive and negative
Tate powers are included. There is no extra characteristic restriction beyond
ell different from p. Scheme universe u is arbitrary and the covering index
universe v is independent; the actual pro-etale object and morphism universes
remain u+1 and u. The fixed module coefficients lie in u+1 as required by that
site, with no equality imposed on site universes and no hidden smallness binder.

Independent searches used the prescribed wrapper: LeanFinder for "A morphism
between local systems on the affine line is determined by its restriction to
the unit section" returned general scheme/sheaf extensionality results, not
this statement; Loogle `AlgebraicGeometry.AffineSpace` returned the existing
construction and its structural maps, which are reused. LeanSearch for
"isomorphisms of local systems along affine line uniquely determined at a
section" was unavailable (Internal Server Error); this is not evidence of
absence. Wrapper grep for `oneSection_comp_map|affineLine_invariance|a1TateLine`
found no declaration. I also directly searched Mathlib, upstream
`WeilConjectures`, project `lean/Sheaf`, and the upstream-name index for the
proposed declaration names and for affine-line invariance and normalized
comparison gluing. I opened the candidate
`AlgebraicGeometry.Etale.eq_of_leftDerivedUpperStar_oneSection_eq`: it assumes
invertibility in the etale derived category and asserts only equality of two
isomorphisms. Its module explicitly records that the gluing half is absent.
It does not state this node, so replacing the delivery by that existing
statement would fail H3. No duplicate of the delivered proposition was found.

There are no mathematical mismatches to repair. I preserved the Lean module,
the verbatim `lean.statement`, and the permitted added statement dependencies.
The two incompatible old proof imports identified in the worker report were
checked against the finite-coefficient framework: the delivered file consistently
uses that published framework, and does not import both conflicting definitions.
All helper data are constructed from existing operations. The one postponed
theorem is the node itself; its docstring follows all ten DAG proof steps through
the nine numbered paragraphs (the finite clopen construction and its derived
localization are combined). All declarations have source/blueprint docstrings.
The signature has no unbound variable, there is no file-local notation or private
notion, every line meets the 100-character limit, and the node's statement field
is verbatim equal to the theorem signature. The required `scompile.py` compiled
the only delivered module cleanly, without an error or warning. The second
reading adds this independent report only; no statement correction is needed.
