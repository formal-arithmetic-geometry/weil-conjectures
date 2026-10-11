## Worker report

The module `Sheaf.AlgebraicGeometry.GlobalHomAdjunction` states
`AlgebraicGeometry.schemeGlobalDerivedHom_adjunction`, with a `sorry` proof.
There are no new definitions or additional nodes.

Hypotheses and clauses:

- X and Y are schemes: `(X Y : Scheme.{u})`.
- X and Y are quasi-compact and quasi-separated: `[CompactSpace X]`,
  `[QuasiSeparatedSpace X]`, `[CompactSpace Y]`, `[QuasiSeparatedSpace Y]`.
- f is a quasi-compact and quasi-separated scheme morphism: `(f : X ⟶ Y)`,
  `[QuasiCompact f]`, `[QuasiSeparated f]`.
- Rf_* preserves D_QCoh: `hpres` is the preservation witness, with the exact
  signature used by `schemeDerivedDirectImage_qcqs_hasRightAdjoint`.
- a is its right adjoint: `a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X`
  and `_adj` is an adjunction from the full-subcategory lift of the shared
  `schemeDerivedDirectImage f` to a. These are supplied as binders because the
  node starts with the right adjoint already given; their existence is exactly
  the dependency theorem. The result holds for any such preservation witness and adjunction.
- P belongs to D_QCoh(X) and K to D_QCoh(Y): the source of each comparison
  functor is `schemeDerivedQCohCategory X` opposite times `schemeDerivedQCohCategory Y`.
  Its full-subcategory inclusions send P and a(K) into D(O_X), and Rf_*P and K
  into D(O_Y), respectively.
- The global derived Hom complexes are the shared `schemeGlobalDerivedHom X`
  and `schemeGlobalDerivedHom Y`. The left side is followed by
  `(ModuleCat.restrictScalars f.appTop.hom).mapDerivedCategory` (with explicit
  ring and localization universe parameters). This is the scalar restriction
  along Γ(Y,O_Y) → Γ(X,O_X) expressly specified in step 2 of the node's proof.
  Without that restriction the two complexes live in different categories.
- Existence and naturality: `Nonempty (leftFunctor ≅ rightFunctor)` is an
  isomorphism of functors, hence a single comparison natural contravariantly
  in P and covariantly in K, rather than a collection of unrelated object isomorphisms.
- `HasDerivedCategory` binders provide the four localizations, with independent
  morphism universes `wX`, `wY`, `wAX`, `wAY`. They are the infrastructure
  binders of the dependency definitions, not extra geometric assumptions.
  All universes and variables are explicitly bound.

Dependencies read and used:

- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`, with full-subcategory
  inclusion `.ι` and Mathlib's object-property `.lift`.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`: `schemeDerivedDirectImage`.
- `Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint`:
  `schemeDerivedDirectImage_qcqs_hasRightAdjoint`; its statement supplies precisely
  the preservation witness and the existence of an adjunction used here.
- `Sheaf.AlgebraicGeometry.GlobalDerivedHom`: `schemeGlobalDerivedHom`; its full
  definition is shared derived internal Hom followed by `schemeDerivedGlobalSections`.
- Mathlib `ModuleCat.restrictScalars`, `Functor.mapDerivedCategory`, and `Functor.prod`
  supply exact scalar restriction on derived categories and the product bifunctors.

Edge cases checked before writing: the empty scheme and zero complexes are not
excluded; no nonempty hypothesis is imposed. There is no boundedness, perfectness,
properness, flatness or Noetherian assumption. Independent localization universes
are retained; the scalar restriction uses the same universe-u modules as the global
Hom definition. For f the identity the comparison is the ordinary global Hom functor
comparison (up to the identity restriction and choice of right adjoint). For affine
schemes the scalar restriction is the usual restriction along the base ring map.

Source read: https://stacks.math.columbia.edu/tag/0B6I (lemma-iso-global-hom,
currently Lemma 48.3.10). The local literature checkout is absent, so the tag was
read online. It states the global Hom isomorphism and proves it by global sections
of the coherator comparison. The module docstring carries both node proof steps,
including the ringed-space composition and coherator detection. No statement
correction or disputed statement is needed; scalar restriction is already spelled
out in the node's proof.

Searches for existing declarations:

- msearch leansearch, `global derived Hom adjunction scheme pushforward`:
  unavailable, Internal Server Error.
- msearch leanfinder, `global derived Hom adjunction right adjoint of scheme derived
  pushforward`: eight hits, all ordinary module/sheaf pushforward adjunctions;
  none states the global derived Hom comparison for a right adjoint to Rf_*.
- msearch loogle, `ModuleCat.restrictScalars, Functor.prod`: no hits, unknown
  identifier `Functor.prod`. Direct source reading found these generic constructions.
- msearch grep, `derived.*[Hh]om.*[Aa]djunction|global.*[Hh]om` in AlgebraicGeometry:
  four unrelated projective-spectrum/global-sections hits, no matching theorem.
- rg in upstream WeilConjectures and project lean/Sheaf,
  `lem-pc-global-hom-adjunction|globalDerivedHom|global.*[Hh]om.*[Aa]djunction`:
  only the project ProperFlatRightAdjointAffineBaseChange proof-docstring reference;
  no matching declaration. Broader searches for GlobalDerivedHom/restrictScalars
  located the shared definition and generic scalar-restriction material.
- Read the full recorded declarations and docstrings of all four statement dependencies,
  and Mathlib ChangeOfRings, Products.Basic and DerivedCategory.ExactFunctor.

Validation: local lcompile passes without warnings. The final delivery dry run
runs the server compile and preflight; the independent second reading is left
for the dispatcher-appointed second reader.

## Second reading by C1

I independently opened the node, the delivered module, all four statement-dependency
nodes and their recorded source modules. The local Stacks checkout is absent. I read
[Tag 0B6I](https://stacks.math.columbia.edu/tag/0B6I) and the original
[duality.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/duality.tex),
including `lemma-twisted-inverse-image`, `equation-sheafy-trace`,
`lemma-iso-on-RSheafHom` and `lemma-iso-global-hom`. The section uses qcqs schemes,
the right adjoint of the restricted unbounded direct image, and quasi-coherent
cohomology, without Noetherian, properness, boundedness or perfectness assumptions.
The node explicitly assumes f qcqs; this adds no geometric restriction beyond its
qcqs source and target. The source specifies the counit-induced comparison; the
node asks for existence of a natural isomorphism, and this is exactly the delivered
conclusion. Its proof docstring describes that canonical construction.

Object, hypothesis and conclusion checklist (each verdict is PASS):

1. X and Y are schemes: `(X Y : Scheme.{u})`. This is Mathlib's scheme, not a
   ringed-space replacement or an affine specialization.
2. X is quasi-compact and quasi-separated: `[CompactSpace X]` and
   `[QuasiSeparatedSpace X]`. Y has the same two binders. These render the node's
   four geometric conditions without a separation or Noetherian strengthening.
3. f is a morphism X to Y: `(f : X ⟶ Y)`, with `[QuasiCompact f]` and
   `[QuasiSeparated f]` as expressly stated by the node.
4. D_QCoh is the full subcategory of D(O) of complexes with quasi-coherent
   cohomology: `schemeDerivedQCohCategory`, via `schemeDerivedQCohProperty` and
   `.ι`, read in `DerivedCategory.lean`. It is not D(QCoh) substituted for this
   full subcategory, and no boundedness constraint is imposed.
5. Rf_* is the recorded `schemeDerivedDirectImage f`, read in
   `SchemeDerivedDirectImage.lean`: the unbounded derived direct image of
   `f.toLRSHom.toShHom`. `hpres` and the ObjectProperty `.lift` give its restriction
   to D_QCoh, precisely as in `schemeDerivedDirectImage_qcqs_hasRightAdjoint`.
   This preservation witness is supplied by the cited theorem, not an additional
   mathematical hypothesis.
6. a is the given right adjoint: `(a : schemeDerivedQCohCategory Y ⥤
   schemeDerivedQCohCategory X)` and `_adj : restricted_Rf_* ⊣ a`. The quantifiers
   allow any such right adjoint and adjunction; existence is supplied by the
   dependency, so no choice or stronger adjunction is imposed.
7. P ranges over all D_QCoh(X), and K over all D_QCoh(Y): both functors have domain
   `(schemeDerivedQCohCategory X)ᵒᵖ × schemeDerivedQCohCategory Y`.
   `.ι.op.prod (a ⋙ .ι)` sends `(op P,K)` to `(op P,a(K))`; the other `.op.prod .ι`
   sends it to `(op (Rf_*P),K)`. Reading Mathlib `Functor.prod` confirms the order.
8. Global RHom is the shared `schemeGlobalDerivedHom` in `GlobalDerivedHom.lean`:
   derived internal Hom followed by unbounded `schemeDerivedGlobalSections`, with
   values in D(Γ(X,O_X)) or D(Γ(Y,O_Y)). I also read the underlying
   `derivedInternalHom` construction; no private notion is introduced.
9. Both global Hom sides have the correct common coefficient ring:
   `(ModuleCat.restrictScalars f.appTop.hom).mapDerivedCategory` on the X side
   restricts Γ(X,O_X)-modules to Γ(Y,O_Y)-modules. Its ring-map direction agrees
   with Mathlib ChangeOfRings and with the explicit scalar restriction in node
   proof step 2. It changes no Hom object by tensor extension.
10. Existence and naturality of the isomorphism: `Nonempty (leftFunctor ≅
    rightFunctor)` provides one natural comparison, contravariant in P and
    covariant in K, for every pair simultaneously. It is not merely an
    objectwise collection, nor does it assert an uncohered sheaf-Hom isomorphism.
11. The four `HasDerivedCategory` binders are exactly the infrastructure needed
    by the recorded scheme and module derived categories. Their morphism
    universes `wX wY wAX wAY` are independent and explicitly bound, as is `u`.
    They do not add geometric assumptions or force the four localizations into
    the same morphism universe. The common scheme universe loses no pair of
    schemes, since both can be represented in a common ambient universe.

Edge cases: empty schemes satisfy the geometric hypotheses and are not excluded;
zero complexes are included in both full subcategories. No characteristic is
specified and the coefficient rings may be zero. There is no index-set binder or
integer parameter that could remove the empty-index or n = 0 cases. Unbounded
complexes and all integer cohomological degrees are retained. Identity morphisms
and affine schemes give the usual comparisons, with ordinary scalar restriction.

Independent searches, using different phrases from the worker:

- `msearch leanfinder "Grothendieck duality global Ext comparison right adjoint
  direct image"`: eight results, ordinary sheaf adjunctions, Gabriel-Popescu and
  condensed modules; none is the scheme global derived-Hom comparison.
- `msearch loogle '"rightAdjoint", "Hom"'`: twelve results, algebra forgetful
  adjoints and generic uniqueness of right adjoints; none states this comparison.
- `msearch grep 'globalDerivedHom|iso_global_hom|derivedHom.*[Aa]djunction'`:
  zero matches.
- Direct `rg` over Mathlib, upstream WeilConjectures and project lean/Sheaf with
  `globalDerivedHom|iso_global_hom|derivedHom.*[Aa]djunction|globalHom.*[Aa]djunction`:
  no matching theorem. Broader Hom/adjunction and global Hom searches found the
  shared global Hom definition, generic tensor-Hom results and an étale category
  adjunction, all different from this theorem.
- `msearch leansearch "global Ext duality isomorphism for right adjoint to derived
  pushforward"`: service unavailable (Internal Server Error), recorded without a
  mathematical verdict. The successful semantic, type/name and direct searches
  above provide the independent existing-declaration check.

No new nodes or dependency modules are present or needed. No statement correction
is present or necessary, so the correction/citer audit does not apply. I found no
mismatch and changed no Lean or node content. The declaration uses only `by sorry`,
introduces no definition, and has no hollow data or additional proved lemma. Both
source docstrings and the two-step proof match the node, including the coherator
and ringed-space composition arguments. Imports serve the adjunction, global Hom,
scalar restriction and product functors; no local notation or hidden let is used.
All variables and universes are bound. The node's recorded signature agrees with
the file. Local lcompile returned exit code 0 without warnings. Final server
compilation and preflight are run by deliver2 below.
