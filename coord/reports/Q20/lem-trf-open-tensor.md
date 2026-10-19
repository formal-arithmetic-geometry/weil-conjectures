## Worker report

This is stage 2, not a second stage-1 split. Q14's reviewed six-step proof split remains
unchanged. The previous worker's refusal concerned a stage-1 deliver.py attempt; the
item still had no Lean declaration. This delivery supplies its statement in
`lean/Sheaf/AlgebraicGeometry/ProEtaleOpenTensor.lean`.

The sole postponed theorem is `AlgebraicGeometry.Scheme.sfOpenTensor`. Its proof is
exactly `by sorry`, and its docstring contains the complete six-step proof plan from
the node. The two fully constructed bifunctors `sfOpenTensorLeft` and
`sfOpenTensorRight` spell out its sides; five instance definitions derive additivity
and exactness from already published theorems and adjunctions. No definition contains
sorry, and no new mathematical theorem is silently proved.

Clause-by-clause comparison:

- The open immersion `j : U ↪ Y` is `{U Y : Scheme.{u}} (j : U ⟶ Y)
  [IsOpenImmersion j]`. This is the dependency's Mathlib open-immersion predicate.
- The finite coefficient ring is `(A : Type u) [CommRing A] [Finite A]`, the same
  finite-ring interface as the recorded intrinsic extension. No characteristic,
  flatness, Noetherianity, geometric-stalk conservativity, finite-type, separatedness,
  or constructibility assumption is introduced. The coefficient-conventions node
  supplies the finite ring; its global finite-field and compact-support constructions
  are not needed to type this finite-ring identity.
- The input category of both bifunctors is exactly the recorded
  `proEtaleDerivedCategory U A ⥤ proEtaleDerivedCategory Y A ⥤ ...`.
  Thus `K` and `M` range over all objects of the intrinsic unbounded categories,
  not bounded or constructible subcategories or selected representatives.
- `j_!` is `(sfIntrinsicExtensionByZero j A).mapDerivedCategory`. It is the recorded
  intrinsic extension, descended termwise using its published exactness instances.
  It is used on the first input of `sfOpenTensorLeft` and on the output of
  `sfOpenTensorRight`.
- `j^*` on the right is `(sfIntrinsicOpenRestriction j A).mapDerivedCategory`.
  Its defining published functor is restriction to the open, transported through
  the same canonical scalar-realization equivalences used to define extension.
  Restriction is exact: left exactness follows from the published j_! adjunction;
  right exactness follows by composing realization equivalences with the published
  restriction/lower-star adjunction. The file supplies these as explicit instances,
  without hypotheses on j, K, or M beyond those in the node.
- The tensor in each side is `curriedTensor` on the unbounded derived category of
  fixed-scalar module sheaves, with `ModuleCat.{u+1} (ULift.{u+1,u} A)` coefficients,
  transported back to the intrinsic constant-ring modules by the published
  `sfIntrinsicModuleEquivalence`. This is exactly the defining body of the recorded
  `ProEtale.derivedTensor`, not an alternative derived tensor. The equivalence is
  the canonical associated-module-sheaf realization of the constant-scalar unit.
  Locally constant scalar sections act by gluing constant scalar actions; the
  tensor universal property therefore identifies its tensor with tensor over A_Y.
  Its exactness transports acyclic complexes and the same K-flat-derived tensor.
  No arbitrary equivalence, coefficient map, or bare Nonempty choice defines either
  bifunctor. In particular the output of each is the intrinsic derived category.
- The displayed direction is `sfOpenTensorLeft j A ≅ sfOpenTensorRight j A`:
  `(j_!K) ⊗ᴸ M ≅ j_!(K ⊗ᴸ j^*M)`.
- `Nonempty` asserts existence of this natural isomorphism of curried bifunctors.
  Its outer and inner naturality squares give simultaneous naturality for every
  derived morphism of K and M. This is stronger than merely asserting a separate
  unrelated objectwise isomorphism, and is exactly the naturality in the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, with site objects in u+1,
  site morphisms in u, and module coefficients in u+1. The module preserves these
  universes and binds u explicitly.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`,
  `AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence` and
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`,
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero_exact` and its three instances.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction`,
  `AlgebraicGeometry.Scheme.sfIntrinsicOpenRestriction` and
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZeroAdjunction`.
- The underlying realization's published exactness declaration is
  `AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization_exact` in
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`; its additive
  conjunct supplies the canonical realization's additive instance. Its inverse
  is additive by Mathlib's `Equivalence.inverse_additive`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`,
  `AlgebraicGeometry.ProEtale.openImmersionRestrictionLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.ProEtale.Derived.Tensor`,
  `AlgebraicGeometry.ProEtale.derivedTensor`: its signature, docstring and defining
  expression `curriedTensor _` were read, including the current server source.
  The recorded finite-level operations in `...Derived.Hom` were also read in full.
  These two alias modules import the legacy `UpperLowerStar.Defs`, whereas the
  recorded intrinsic extension imports `FiniteCoefficient.UpperLowerStar.Defs`.
  Importing both duplicates declarations. The delivered file imports the smaller
  generic monoidal-derived infrastructure and expands the tensor alias's exact
  defining expression; it uses the recorded intrinsic restriction for pullback.
  This avoids a duplicate import without defining another tensor notion or
  changing either dependency record. The full internal-Hom, integral, rational
  and algebraically closed operations are not inputs to this finite-level lemma.

The modules of all other stated proof dependencies are imported without `public`:
pro-etale localization and ringed-open comparison; localized exact module adjunction;
ringed-slice extension tensor; total tensor, K-flatness, flatness, tensor closedness,
K-flat resolutions, inverse image, K-flat pullback preservation, and derived tensor
descent. The Mathlib exact-derived-functor, adjoint-colimit and localized-module
interfaces are imported as well. These imports preserve the six-step future proof plan.
The legacy tensor/Hom alias imports are the two intentional omissions explained above.

The item gains the two already landed statement dependencies
`lem-weil-extension-by-zero-adjunction` and `lem-weil-extension-by-zero-exact`,
whose recorded definitions and exactness instances are required by the statement.
There are no new nodes, dependency modules, statement corrections, or edits to the
reviewed proof and proof_deps. No statement dispute was found.

Edge cases checked before drafting: U empty and Y empty; j the identity; K=0 or M=0;
the zero finite coefficient ring; a nonflat M; complexes unbounded in both directions.
Restriction/extension remain the same exact functors in these cases, and the K-flat
construction computes the tensor without any boundedness or flatness assumption on
M. For j=id the statement is the ordinary tensor identity; for the empty open both
sides vanish. Nothing forces the site's object universe to equal its morphism universe.

Sources read: the complete blueprint node at order 2160 and its two proof paragraphs,
the containing unit record, Stacks `sites-modules.tex`, Tag 0E8I
`lemma-j-shriek-and-tensor` (including its Hom-adjunction argument), and
`sites-cohomology.tex`, Tag 0GL1 `lemma-j-shriek-and-tensor`. The latter explicitly
allows all objects of the unbounded derived categories. The six-step docstring also
spells out preservation of flat terms, the signed total differential, homotopy
compatibility, and separate localization on the two sites.

Existing-statement searches executed for this worker (exact service queries and
results are retained in searches.jsonl):

- LeanFinder: “Extension by zero along an open immersion of small pro-etale sheaves
  of modules commutes with unbounded derived tensor product”: eight light-condensed
  monoidal/flatness hits, none this intrinsic pro-etale identity.
- Loogle: `"projection", "tensor"`: zero hits.
- Mathlib grep: `extensionByZero|lowerShriek|openImmersion.*[Tt]ensor` in
  `CategoryTheory`: zero hits.
- LeanSearch: “Extension by zero commutes with the unbounded derived tensor product
  of sheaves of modules”: unavailable, Internal Server Error. This is not evidence
  of absence.
- `rg` in the source project for the exact item id found no declaration. Searching
  open-immersion projection names found
  `ProEtale.derivedOpenImmersionLowerShriekProjectionIso` and its underived analogue.
  I read the full source of the derived projection module. It concerns an abstract
  fixed-scalar sheaf category and asks for `UpperStarPreservesFlat A`; it does not
  directly state the intrinsic coefficient-category formula recorded by this item.
  The existing-declaration shortcut would omit the coefficient realization that
  this delivery explicitly supplies. Its reverse orientation alone would not
  be an obstruction, since an isomorphism can be inverted.
- `rg` in `lean/Sheaf`, Mathlib, the source repository and the upstream name index
  found no existing `sfOpenTensor*` declarations and no intrinsic open tensor formula.
  Existing intrinsic extension, restriction and realization declarations were reused.

Validation: the delivered module compiled cleanly through the prescribed scompile.py
wrapper, both in its sandbox and as its library module, with no unexpected warning.
The required `deliver2.py Q20 lem-trf-open-tensor --no-push` printed OK: the delivery
compiles and passes preflight except for the independent second reading, which the
second reader writes; nothing was pushed. No second-reading section is fabricated here.

A separate scratch import probe confirmed the legacy-import diagnosis both locally
and in server confirmation: importing the recorded legacy tensor module with the
intrinsic extension fails because the environment already contains
`AlgebraicGeometry.ProEtale.lowerStarComp` from the finite-coefficient module. The
scratch probe is outside lean/ and is not part of the delivery.

## Second reading by Q20

I did not write the statement. I independently read the base node and sandbox node,
the complete delivered module, the blueprint lemma and its containing unit, and
Stacks `sites-modules.tex`, lemma-j-shriek-and-tensor (0E8I), and
`sites-cohomology.tex`, lemma-j-shriek-and-tensor (0GL1), including their surrounding
localization discussion. The Stacks statements assume a ringed site and an object
of that site; the derived statement explicitly quantifies over arbitrary objects
of the unbounded derived categories. They impose no finiteness, flatness,
boundedness, characteristic, or nonemptiness hypothesis on the two complexes.
The blueprint specializes to an open immersion and finite coefficients. Its
finite-type/finite-field application in the containing unit introduces no extra
hypothesis needed by this tensor identity.

My object/hypothesis/conclusion checklist, matched against the Lean:

1. Schemes U and Y, and an open immersion j from U to Y: the binders
   `{U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]`. I opened Mathlib's
   `IsOpenImmersion`, which abbreviates the locally ringed space open-immersion
   predicate. Verdict: the same objects and hypothesis, without a base field,
   separatedness, finite type, or Noetherianity assumption.
2. A finite commutative coefficient ring A: `(A : Type u) [CommRing A] [Finite A]`.
   I read `def-trf-coefficient-conventions`, `def-weil-extension-by-zero`, and
   `def-weil-derived-tensor`. The tensor lemma uses the finite ring, not the
   compact-support or Frobenius datum also packaged by the conventions node.
   Stacks proves the identity for arbitrary ringed sites, so the generic finite
   ring interface covers, in particular, every A_{E,n} in that application.
   Verdict: correct coefficients, with no field or invertibility substitution.
3. The small pro-etale sites and constant ring sheaves: both bifunctors have domain
   `proEtaleDerivedCategory U A ⥤ proEtaleDerivedCategory Y A`. I opened
   `ProEtaleDerivedCategory`, `proEtaleConstantRing`, and `proEtaleRingModules`:
   these use precisely the constant CommRingCat sheaf, forgotten to RingCat,
   and `SheafOfModules`, with the standard unbounded derived category.
   Verdict: the recorded intrinsic categories, not etale, condensed, completed,
   bounded, or constructible categories.
4. K ranges over D(U,A), and M over D(Y,A), with no further conditions. They are
   the two inputs of these curried bifunctors. Verdict: all objects and all
   derived morphisms, in the correct order; no selected representatives.
5. Extension by zero on the left and outside the right-hand tensor is
   `(sfIntrinsicExtensionByZero j A).mapDerivedCategory`. I read its defining
   composite, the canonical realization equivalence, the exactness theorem and
   its instances. The middle fixed-scalar functor is the localization extension
   presheaf followed by sheafification. Verdict: the dependency's actual j_!,
   applied termwise by exactness, with no new extension functor.
6. Pullback in the right-hand tensor is
   `(sfIntrinsicOpenRestriction j A).mapDerivedCategory`. I read the restriction
   and intrinsic adjunction definitions, the fixed-scalar sectionwise restriction,
   `upperStarIsoOpenImmersionRestriction`, and the intrinsic finite pullback
   interface. Restriction is the sectionwise inverse image for an open immersion,
   transported by the same coefficient equivalences; exactness makes its
   termwise descent the derived pullback. The three retained instances provide
   additivity and finite-limit/finite-colimit preservation from the published
   adjunctions, without an added assumption. Verdict: the required j^*.
7. Derived tensor over A on each site is `curriedTensor` on the derived category
   of fixed-scalar module sheaves, conjugated by the canonical realization.
   I opened the full recorded `ProEtale.derivedTensor`, including its universes
   and instance hypotheses: its body is exactly `curriedTensor _` for the global
   K-flat-derived monoidal structure. I also read the realization's actual data:
   module presheaf construction and associated-module-sheaf construction along
   the constant-scalar sheafification unit. Locally extending scalar actions
   identifies the ordinary tensor universal properties, and the exact equivalence
   identifies their K-flat-derived tensors. Verdict: the same derived tensor,
   with real coefficient transport; neither an arbitrary monoidal structure nor
   an unconstrained comparison is assumed. Expanding the recorded alias avoids
   the documented clash between legacy and finite-coefficient functor imports.
8. Left side `(j_!K) ⊗ᴸ M`: `sfOpenTensorLeft` first applies derived extension to K,
   takes both arguments back through the Y realization inverse, tensors there,
   and realizes the result on Y. Right side `j_!(K ⊗ᴸ j^*M)`:
   `sfOpenTensorRight` restricts M, takes both arguments through the U realization
   inverse, tensors on U, realizes on U, and extends to Y. I checked Mathlib's
   `whiskeringLeft₂` and `postcompose₂` definitions for this evaluation order.
   Verdict: every operation, argument, and output site is in the stated place.
9. Existence and simultaneous naturality of the displayed isomorphism:
   `Nonempty (sfOpenTensorLeft j A ≅ sfOpenTensorRight j A)`. An isomorphism in
   this functor category supplies a natural isomorphism in M for each K and
   naturality in K; its components are the claimed objectwise isomorphisms.
   Verdict: exactly a natural isomorphism, with the displayed orientation;
   it does not assert equality or an extra normalization.

Edge cases: there is no nonempty assumption on U or Y. For the empty open both
sides are zero; for the identity open the formula is the tensor identity. Zero K,
zero M, and the zero finite ring are included. Unbounded and nonflat M are included
because the tensor is derived. There is no index-set restriction. There is no n
binder: all finite coefficient rings cover the prescribed n >= 1, and even the
zero-ring n = 0 specialization remains well typed. No characteristic is excluded.
The explicit universe u is arbitrary; the recorded small site still has objects
in u+1 and morphisms in u, and modules/scalars in u+1 using ULift A. No equality
between those site universes or additional smallness instance is imposed.

Independent H4 searches used different wording from the author's:

- LeanFinder: "Natural projection formula for exact extension along an open
  subtopos and derived tensor on sheaves of modules" returned eight condensed
  monoidal/flatness and cartesian-closed sheaf declarations, none this statement.
- Loogle: `"lowerShriek"` returned zero hits.
- LeanSearch: "For sheaves on an open subscheme, extension by zero commutes with
  derived tensor and restriction" succeeded, returning ordinary ringed-space
  restriction and Scheme.Modules restriction/tilde declarations; none is the
  unbounded pro-etale statement. This independently resolves the author's earlier
  unavailable LeanSearch service; its failure was not used as absence evidence.
- The prescribed grep service query
  `j_shriek|extensionByZero.*tensor|openImmersionLowerShriekProjectionIso|sfOpenTensor`
  returned zero hits. I additionally ran rg directly over Mathlib, all of
  WeilConjectures, and lean/Sheaf, for extensionByZero/tensor, projectionIso,
  projectionFormula, shriek/tensor, and intrinsic tensor names.
- I opened the actual upstream
  `ProEtale.derivedOpenImmersionLowerShriekProjectionIso`, its two bifunctors,
  and its surrounding variable declarations. It is a fixed-scalar formula with
  the `UpperStarPreservesFlat A` interface and left-derived upperStar; it does
  not expose this statement on intrinsic constant-ring modules. Its opposite
  orientation is harmless, but the coefficient/functor transport is real work.
  The existing-declaration shortcut therefore does not replace this module.

Mismatch found and repaired: the author's realization-additivity instance repeated
the already published
`Scheme.sfIntrinsicModuleEquivalence_functor_additive` in
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`; its inverse-additivity
instance also repeated Mathlib's global `Equivalence.inverse_additive`. I removed
`sfOpenTensorRealization_additive` and
`sfOpenTensorRealizationInverse_additive`, imported the existing finite-operations
module, cited its owning node `def-weil-pbc-proetale-operations` in stmt_deps, and
removed the two names from lean.declarations. Thus the module has three instance
bridges, not the five described in the historical worker report above. This is
interface reuse only: no node statement, theorem signature, tensor bifunctor,
proof step, or mathematical hypothesis changed. No other mismatch was found.

There are no new nodes, dependency modules, or statement_change records to review.
I checked the six-step theorem docstring against all six node proof steps: site
and coefficient identification; the underived formula; coproduct totalization and
its signed differential; K-flatness and flat terms; representative computation;
and homotopy-compatible descent with simultaneous naturality. Every declaration
has a source and the blueprint id, all data definitions have actual bodies, and
the sole theorem has proof `by sorry`. The node's lean.statement is verbatim the
file signature. All variables and universes are explicitly bound, and no local
notation, private definition, local instance, or hidden let occurs in the statement.

Validation after my repair: the prescribed scompile.py compiled the sole delivered
file successfully both as a sandbox file and as its library module, with no error
and no warning. I also checked the verbatim recorded signature, 100-column limit,
and that sfOpenTensor is the sole postponed theorem in the file.
