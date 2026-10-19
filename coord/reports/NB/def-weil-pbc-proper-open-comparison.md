## Worker report

The module Sheaf.AlgebraicGeometry.ProperOpenComparison defines the canonical comparison
AlgebraicGeometry.Etale.properOpenComparison, including its section and specified theta.
No node statement or dependency record changes. There are no new independent notions.

Hypotheses and clauses:
- T₁, T₂, X are Scheme.{u}; f is u, with [IsProper f]. The two maps j₁ and j₂ have
  [IsOpenImmersion j₁] and [IsOpenImmersion j₂]; h : j₁ ≫ f = j₂ is the required triangle.
- Λ : Type (u+1), [CommRing Λ], [Finite Λ] express finite commutative coefficients in
  the recorded six-functor encoding; K belongs to DerivedCategory.Plus of module sheaves
  on X.smallEtaleTopology. There is no boundedness or geometric hypothesis beyond the node.
- V is pullback f j₂; b and p are pullback.fst and pullback.snd. properOpenSection is
  literally pullback.lift j₁ (𝟙 X), using h for its commutativity proof. Its two projection
  equalities are the library pullback.lift_fst and pullback.lift_snd.
- properOpenSectionGeometry states the node's geometric assertions needed to form the
  comparison: s is open, its image is closed, and the square (id,s,j₁,b) is Cartesian.
  This is the only postponed theorem; its docstring supplies the complete argument
  already in this definition node. It is recorded in lean.declarations for this node.
  The identification of V with the inverse-image open is the usual base-change-of-open
  interpretation of pullback.fst, as used in that argument, not an extra chosen map.
- properOpenIdentification's r is asIso of derivedBaseChangeMapPlus, using the exact
  recorded isIso_derivedBaseChangeMapPlus_of_openImmersion on the canonical pullback square.
- Its e is extensionZeroBaseChangeDerivedPlusIso on the identity-top square followed by
  s_! applied to upperStarIdDerivedPlus. Thus identity inverse image is identified with
  the identity, rather than left as a different object.
- Its c is the component of the natural isomorphism characterized by
  clopenSectionDirectImage, with closed-image and section equations supplied. Choice
  is from that characterized isomorphism, not a mere Nonempty isomorphism. Its equation
  fixes c after composition with isomorphisms, so c is unique.
- Theta is r ≪≫ Rp_*.mapIso e ≪≫ c, exactly the specified composite in Lean's order.
- Alpha is j₂!.map theta.inv followed by the counit of
  derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus. Its source is j₂! K and its
  target is Rf_* j₁! K, in the indicated D⁺ categories. The existing descended exact
  adjunction supplies the counit, with no arbitrary adjunction or map as parameter.

Dependency declarations used:
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: IsProper and its pullback instance.
- Mathlib.AlgebraicGeometry.OpenImmersion: IsOpenImmersion, its base-change instance.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback, fst, snd, lift.
- Sheaf.AlgebraicGeometry.DerivedCategories: the recorded module-sheaf D⁺ encoding.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: upperStar, lowerStar and their
  adjunction; Derived.UpperLowerStarCoherence: rightDerivedLowerStarPlus,
  upperStarIdDerivedPlus.
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs:
  openImmersionLowerShriek, openImmersionLowerShriekUpperStarAdjunction and exactness.
- Sheaf.AlgebraicGeometry.DerivedOpenRestriction:
  isIso_derivedBaseChangeMapPlus_of_openImmersion; the canonical map itself is in
  WeilConjectures.SixFunctors.BaseChange.Derived.
- Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange:
  extensionZeroBaseChangeDerivedPlusIso, rendering the OpenImmersionSquare property
  defined in Sheaf.AlgebraicGeometry.OpenImmersionSquare.
- Sheaf.AlgebraicGeometry.ClopenSectionDirectImage: clopenSectionDirectImage.
- Sheaf.AlgebraicGeometry.OpenSectionClopen: open_section_clopen, the geometry proof input.
- WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek:
  derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus, the existing derived adjunction.
- Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact,
  WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction and
  WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor give the recorded
  exactness, termwise descent and boundedness interfaces; localization is the Mathlib
  Localization.lift/liftNatTrans interface used by the existing descended constructions.

Edge cases checked before writing: empty X gives the unique map between the indicated
zero extensions; zero K and the zero coefficient ring remain allowed. Identity f, j₁=j₂,
including the identity open, use the same canonical exchanges and counit, without extra
choices. Non-surjective proper f and the extra clopen complement of s in V are retained;
no claim that s fills all of V is assumed. All scheme and coefficient universes follow
exactly the recorded site and derived category size convention. No auto-bound variables.

Searches: msearch.py leanfinder "proper map fixing an open subscheme comparison extension
by zero derived direct image" returned eight unrelated scheme lift/restriction hits;
none is this comparison. msearch.py loogle "CategoryTheory.Adjunction.homEquiv" returned
12 generic adjunction declarations, including the counit formula; no geometric map.
msearch.py grep "properOpenComparison|proper_open_comparison|properOpenIdentification"
returned zero hits. Direct rg of the upstream WeilConjectures and side lean/Sheaf for
properOpen, proper_open and this blueprint id returned no hits. Read the blueprint
source file and the recorded comparison modules in full. No duplicate notion found.

Validation: scompile.py compiled this module cleanly against the side overlay and live
library (each file separately). Only properOpenSectionGeometry has a sorry; all data
are explicit pullback, canonical exchange, characterized component restriction and
counit constructions. No STATEMENT-DISPUTED issue or node correction.

## Earlier second reading (a previous round; superseded)

Pending: the dispatcher supplies an independent second reader after this worker handoff.
This placeholder records no independent approval; no delivery push has been performed.


## Second reading by NB

Independent second reader, 2026-10-15. Read the repository node and sandbox node,
the delivered module, and the blueprint source at
sec-smooth-purity/sk-def-sf-operations/def-weil-pbc-proper-open-comparison.md,
together with the neighbouring source lem-weil-pbc-proper-open-identification.md.
The source of this item is the blueprint, not a Stacks lemma. Its conventions are
schemes, finite commutative coefficients as in the dependency defining D, and D+;
there is no ambient field, Noetherian, characteristic, or finite-dimensional hypothesis.
No statement_change is present or needed. No new nodes or dependency modules are delivered.

Object/hypothesis/clause checklist, written independently from the node:

1. Schemes T1,T2,X: `{T₁ T₂ X : Scheme.{u}}`. PASS: Mathlib Scheme and Hom,
   not varieties or schemes over an implicit field. Read their definitions in Scheme.lean.
2. Proper u: `(f : T₁ ⟶ T₂) [IsProper f]`. PASS: read IsProper in
   Mathlib.AlgebraicGeometry.Morphisms.Proper; separated, universally closed and locally
   finite type, with quasi-compactness implied by universal closedness. No extra assumption.
3. Two open immersions from the same X and commuting triangle: `(j₁ : X ⟶ T₁)` and
   `(j₂ : X ⟶ T₂)` with both IsOpenImmersion instances and `h : j₁ ≫ f = j₂`.
   PASS: read Mathlib's locally-ringed-space open-immersion definition; the sheaf maps
   are included, not merely a condition on underlying spaces.
4. Finite commutative ring and bounded-below complex: `Λ : Type (u + 1)`, CommRing,
   Finite, and `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
   (ModuleCat.{u + 1} Λ))`. PASS: read DerivedCategories.lean and its coefficient
   encoding. These are the recorded constant-coefficient module sheaves, not O_X-modules.
   No bounded-above, constructibility, torsion-freeness or invertibility assumption.
5. V,b,p: `pullback f j₂`, `pullback.fst f j₂`, `pullback.snd f j₂`. PASS:
   these are the recorded chosen scheme fibre product and its projections.
6. Specified s and both projection equations: `properOpenSection` is literally
   `pullback.lift j₁ (𝟙 X) ...`; lift_fst gives s ≫ b = j1 and lift_snd gives
   s ≫ p = id. PASS: the comparison does not accept a free section as input.
7. V is the inverse-image open and s is its indicated sub-open: PASS. Read Mathlib
   OpenImmersion.lean, including the base-change projection instances and
   range_pullback_fst/opensRange formulas. The first projection identifies V with
   f inverse-image of j2's range; its composite with s is j1 as a scheme morphism.
   The named `properOpenSectionGeometry` records s's open immersion and closed image;
   p's properness is the Mathlib base-change instance from Proper.lean. Its docstring
   derives closedness using the recorded `open_section_clopen`, whose signature was read.
   Omitting a redundant separate inverse-image identification datum loses no clause.
8. Identity-top square Cartesian: `properOpenSectionGeometry ... |>.2.2` has
   `IsPullback (𝟙 X) s j₁ b`. PASS: the docstring gives the universal property using
   monicity of b, exactly the node's argument. Read OpenImmersionSquare and
   ChosenCartesianSquare: the property used by the recorded exchange is the same square.
9. r: `asIso (derivedBaseChangeMapPlus ... sq.toCommSq)`, component at j1!K.
   PASS: sq uses the identity identification of the chosen pullback; read
   DerivedOpenRestriction.lean and BaseChange/Derived.lean. The IsIso theorem has exactly
   this canonical transformation, not an existential exchange chosen arbitrarily.
10. e: `extensionZeroBaseChangeDerivedPlusIso Λ geom.2.2`, followed by s! applied
    to `upperStarIdDerivedPlus`. PASS: read the delivered dependency's actual construction
    as the localized inverse adjunction mate and the identity-inverse-image construction
    in UpperLowerStarCoherence.lean. The source and target are precisely b* j1!K and s!K.
11. c: `(clopenSectionDirectImage Λ p s ... ...).choose.app K`. PASS: read this
    theorem in full. Its equation prescribes component restriction after composition with
    the unit isomorphism and functor-factorization isomorphisms. Cancellation uniquely
    determines each component, hence the natural isomorphism. This is permitted choice
    from a characterization, not data chosen from bare Nonempty.
12. Theta: `r ≪≫ Rp_*.mapIso e ≪≫ c` in `properOpenIdentification`. PASS:
    exact order and objects, including the identity normalization in e.
13. Induced D+ adjunction: the recorded sheaf `openImmersionLowerShriekUpperStarAdjunction`
    gives `derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus`. PASS: read its
    construction and the generic mapDerivedCategoryAdjunction/PlusAdjunction definitions.
    The generic unit factorization theorem identifies this with the termwise homotopy
    unit followed by localization, so this is the specified induced adjunction. All
    coefficient resolution/monoidal instances are supplied for ModuleCat; none is a new
    hypothesis on f, Lambda or K. Read the recorded mapHomotopyCategory, Localization.lift,
    liftNatTrans, and exact-functor homology signatures as well.
14. Alpha: `j₂!.map (properOpenIdentification ... K).inv ≫ adj.counit.app ...`.
    PASS: the source is j2!K and target Rf_*j1!K, exactly the adjoint of theta inverse.
    Every composite is in the stated D+ category; no arbitrary adjunction is a parameter.

Edge cases: empty X, empty schemes wherever the given maps exist, the zero object K,
the zero coefficient ring, identity f and identity opens, and a nonempty extra complement
of s(X) in V are all permitted by the binders and constructions. No assumption identifies
s(X) with all of V. There is no index type or degree n to restrict; D+ allows every lower
bound, including complexes with nonzero H^0. All characteristics are allowed. Universe u
is arbitrary; the u+1 coefficient convention is exactly the dependency's site encoding,
not an added equality between independently given site universes. No unbound variables.

Independent searches used different conceptual wording from the author:
- msearch leanfinder: "adjoint morphism extension by zero proper pushforward restriction
  inverse isomorphism" returned eight Zariski module restriction/adjunction hits; none
  defines this etale D+ comparison.
- msearch loogle: `CategoryTheory.Adjunction.homEquiv_counit` returned the generic
  adjunction transpose formula only. It confirms the implemented order.
- msearch grep: `fixing an open|properOpen|proper_open|restriction.*clopen` returned
  no hits. Direct rg over upstream WeilConjectures, side lean/Sheaf and Mathlib for
  properOpen/proper_open/fixing-an-open and alternate proper/comparison terms found
  generic Zariski comparisons and pro-etale f! to f* comparisons with other domains,
  not this map. No duplicate definition or usable exact existing declaration found.

Mismatch and repair: the alpha docstring wrote `ε ≫ j₂!(θ⁻¹)` while calling this
functional composition order. Replaced the symbol by `ε ∘ j₂!(θ⁻¹)`; the actual
Lean body already applies j2! to the inverse before the counit and is correct.
No mathematical declaration, signature, node statement, or dependency record changed.
The named geometry theorem remains the sole postponed proof, with its matching
assertions in this definition node and complete geometric argument in its docstring.
All definitions have real data; no theorem has been proved. The node lean.statement
matches the main signature verbatim in the delivery reader's format.

Validation: scompile.py NB def-weil-pbc-proper-open-comparison with the absolute
sandbox module path passed both sandbox and library-path checks (2.2 seconds each),
without errors or warnings. Only the prescribed wrapper was used; no global build.
