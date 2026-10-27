## Worker report

Module: `Sheaf.SixFunctors.RelativeHomChangeOfPresentation`.
Main statement: `AlgebraicGeometry.ProEtale.relativeHom_changeOfPresentation`.
The sole postponed proof is that theorem, with the node's complete five-step proof
in its docstring. Its conclusion is the requested identity for every g, conjoined
with bijectivity of each of the four specified factors. There are two real-data
helpers: the positive-level finite-ring instance (just the existing dependency
proof), and `relativeHomPresentationComparison`, the displayed composite B_G.
No node statement, proof, dependency list, or other inherited field was changed.
No new definition node or dependency repair was necessary.

Clause-by-clause rendering:

- The global p, q, k_0 and algebraic closure k are `D : FiniteFieldDatum.{u}`.
  `l`, `[Fact l.Prime]`, and `_hl : l ≠ D.p` give the coefficient prime.
  `E : Type (u+1)` with `Field`, `Algebra (Padic l) E`, and `FiniteDimensional`
  gives the finite extension. `n : ℕ` and `[Fact (1 ≤ n)]` cover exactly all
  positive levels; the named instance uses `hn.out`, not a new assumption of
  finiteness. Every occurrence of A is literally `Padic.coefficientExtensionRing
  l E n`, using the recorded valuation ring and chosen uniformizer.
- Schemes have their actual small-site universe `u`; module values and
  coefficients have universe `u+1`. The categories are the ordinary
  `DerivedCategory (Sheaf ... (ModuleCat.{u+1} A))`, the fixed-ring coordinates
  used by the recorded comparison-class adjunction. `G`, `M` use `DerivedCategory.Plus`.
  This keeps the actual small sites and imposes no equality of object and
  morphism universes and no constructibility or Tor hypothesis.
- `aX`, `aY` are the structure maps to `Spec D.k`; each has `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact`. `f` has the same three morphism
  properties, and `_hf : f ≫ aY = aX` expresses the k-morphism condition.
- `c : Compactification f` retains j=`c.i`, p_c=`c.g`, and ambient `c.Z`.
  `d : ℕ` expresses an integer d≥0 without excluding any such integer.
  `_hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)` is the exact dimension bound,
  including the empty ambient scheme of dimension bottom.
- F_c is `Etale.rightDerivedLowerShriekOfCompactification (ModuleCat A) c`;
  P_c is `ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat A) c`.
  These are the ordinary fixed-ring expressions Rp_* j_! used in the statement's
  canonical comparison and relative Hom interface. The intrinsic ringed encoding
  of `sfIntrinsicCompactSupport` is not mixed into this fixed-ring Hom chain.
- `Ic` and `adjc : F_c ⊣ Ic` retain the specified etale right adjoint and adjunction.
  `Φ : ComparisonClassAdjunction A f c Ic adjc (DerivedCategory.plusEtaleOrigin ... X)
  DerivedCategory.TStructure.t.plus` is the existing datum of the specified bounded
  relative bijections. In particular its `homEquiv_normalized` field fixes the
  four-factor chain for this very `adjc`; it is not an arbitrary Hom equivalence
  or a hypothesis asserting this delivery's conclusion. The datum includes the
  established compactification coherence of the dependency. Its `homEquiv c`
  is the statement's Phi^c.
- `F`, `Q`, `I` have exactly the four ordinary ambient categories specified in
  the node. `e : F_c ≅ F`, `q : P_c ≅ Q`, and `β : F ⊣ I` are arbitrary specified
  presentations and adjunction. No pro-etale adjunction is assumed.
- r is used directly as `conjugateIsoEquiv adjc β e.symm`, which is the actual
  Mathlib adjunction conjugate of e inverse. Its hom is `conjugateEquiv adjc β e.inv`.
  `conjugateEquiv_counit` has exactly the node's characterization, in Lean order:
  `F.map (r.hom.app N) ≫ β.counit.app N = e.inv.app (Ic.obj N) ≫ adjc.counit.app N`.
  There is no unconstrained auxiliary map or extra counit assumption.
- S_T is `(comparisonUpperStar (ModuleCat A) T).mapDerivedCategory`;
  U_T is `(comparisonLowerStar (ModuleCat A) T).rightDerivedFunctor`;
  eta is the actual `(derivedComparisonAdjunction (ModuleCat A) Y).unit`.
  `_hFG`, `_hIU` render precisely FG and I U_Y M being bounded below.
- `relativeHomPresentationComparison` defines B_G as
  `S_Y.mapIso (e.app G.obj).symm ≪≫ C_G.symm ≪≫ q.app (S_X.obj G.obj)`.
  Here C is the existing `fixedCompactSupportComparisonIso A c`, the normalized
  canonical comparison used literally by `Φ.homEquiv_normalized` and
  `specifiedExceptionalHomEquiv`. Its construction, read at
  `FiniteComparisonClassAdjunction.lean:151`, is the exact open comparison and
  the proper direct-image counit mate, with the canonical derived and D+
  compatibility isomorphisms. `compactSupportSiteComparison` has the same source,
  target, orientation, exact open comparison and proper counit mate, assembled
  using bounded-below compatibility first. This is the same canonical comparison
  in the normalization already recorded by the dependency, not a freely chosen C.
- The main universal quantifier ranges over every `g : Q(S_X G) ⟶ M`.
  Its left side is `Φ.homEquiv c ... (q.hom.app _ ≫ g) ≫ S_X.map (r.hom.app (U_Y M))`.
  Its right side is `S_X.map (β.homEquiv G.obj _ (eta.app (F.obj G.obj) ≫
  U_Y.map (B_G.hom ≫ g)))`. Lean's `≫` reverses the printed composition order
  relative to the TeX convention; both sides have source S_X G and target S_X I U_Y M.
- The four following `Function.Bijective` conjuncts are respectively:
  precomposition with B_G; b ↦ eta ≫ U_Y(b); `β.homEquiv`; and `S_X.map` on
  Hom(G, I U_Y M). Thus none of the node's four bijectivity assertions is lost.
  Their naturality comes from the existing natural comparison, adjunction Hom
  maps and functor Hom map. The comparison datum supplies naturality for Phi.
- The supplied origin proof is
  `DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj G.property`.
  It is the canonical image with identity isomorphism; no arbitrary antecedent,
  witness choice, or conjugating map is introduced.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its public coefficient-extension
  module supplies `Padic.coefficientExtensionRing` and the ring/ideal/uniformizer.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: ordinary module derived
  categories. Mathlib `DerivedCategory.Plus` and `TStructure.t.plus` give D+.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: ringed coefficient module
  categories and their fixed-ring realization; no duplicate category is defined.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus` and its underlying `comparisonUpperStar`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `proEtaleSiteComparisonModules`;
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison`:
  `derivedComparisonAdjunction`, `DerivedCategory.plusEtaleOrigin`, and its
  canonical image proof, plus the bounded-below fully faithful Hom theorem.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`:
  `isIso_compactSupportComparisonUnit`, the recorded full-faithfulness interface.
- Convention node `def-weil-scheme-morphism-properties`: Mathlib `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`. It defines no separate declaration.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification`,
  with the original `Defs` structure and retained open/proper factorization.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` and its pro-etale
  finite-coefficient counterpart: the two `rightDerivedLowerShriekOfCompactification`s.
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom` publicly exposes
  `ComparisonClassAdjunction` from `EtaleOriginAdjointClass`, its `homEquiv` and
  `homEquiv_normalized`; `FiniteComparisonClassAdjunction` supplies
  `fixedCompactSupportComparisonIso`. Read also the fixed finite exceptional
  composite `sfFiniteExceptionalAt`, reexported by the recorded
  `ConstructibleExceptionalAdjunctionCoefficients` interface. Integral/rational
  System data are not required for this finite-level statement.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `conjugateIsoEquiv`, `conjugateEquiv`,
  and the counit component formula.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparison`, checked against the normalized comparison above.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `Scheme.FixedEtaleOriginWitness` retains the pair; at the image G the antecedent
  is G and its isomorphism is the identity, represented by the existing origin proof.

Searches actually run (all with msearch.py NC and this item):

- LeanFinder: “The specified bounded etale proetale exceptional Hom equivalence
  respects change of compact support presentation and the counit compatible right
  adjoint conjugate”. Eight results, mostly condensed adjunctions and
  `StandardEtalePair.homEquiv`; no matching statement.
- Loogle: `CategoryTheory.conjugateEquiv, CategoryTheory.Adjunction.homEquiv_naturality_left`.
  Zero hits for this combined query. The local Mates source does provide the
  individual conjugation equivalence, which is used directly.
- LeanSearch: “Change compact support presentations in the specified etale proetale
  derived exceptional Hom bijection using the adjunction conjugate”. Eight hits,
  including `conjugateIsoEquiv_apply_hom` and sheaf pullback adjunctions; none is
  this derived-site four-factor identity.
- Mathlib grep via msearch:
  `relativeHom.*presentation|relative_hom.*presentation|conjugateEquiv.*homEquiv`
  in CategoryTheory. One bicategorical mate-identity proof hit, no exact statement.
- rg with that expression in `lean/WeilConjectures` and `lean/Sheaf` found generic
  mate-transpose statements, not this identity. The node-id search in both trees
  found no existing declaration. Additional searches for `relativeHom`,
  `fourFactor`, `sfFiniteExceptionalAt`, and `fixedCompactSupportComparisonIso`
  located the actual dependency interfaces used above.

Edge cases checked: n=1 is included; n=0 is excluded exactly as in the node.
Empty X, Y, or c.Z needs no nonempty assumption or maximum; Krull dimension bottom
satisfies the nonnegative bound. d=0 is included. Zero G or M and identity e/q
make each typed Hom map meaningful; identity origin has no conjugation. Nontrivial
scalar rescaling of e or the etale adjunction changes r through conjugation, so
no accidental assumption that adjoint identification is the identity is made.
No unbounded pro-etale exceptional adjunction, full faithfulness on arbitrary
unbounded targets, constructibility, or Tor bound is asserted.

Validation: scompile.py checked the complete module separately in sandbox and
library mode, both clean (8.6 s / 8.3 s on the clean run). Every universe and
variable is explicitly bound and autoImplicit is disabled. No statement dispute.

## Second reading by NC

I reread the node, source four-factor display, final comparison paragraph, and
finished Lean signature, concentrating on direction of the three isomorphisms and
on which adjunction is specified. This is a second pass by the assigned worker;
the maintainer supplies the independent delivery review as the dispatcher brief
specifies. No other agent was started.

The chosen `ComparisonClassAdjunction` retains adjc and its normalization, unlike
an arbitrary natural Hom bijection; its P/Q domain is exactly bounded-below etale
origin / bounded below. The source and target of the main equality are S_X G and
S_X I U_Y M. q occurs forward on the left. e occurs inverse in B and in the
conjugate; C occurs inverse in B. The comparison unit is the actual derived unit.
The four bijective factors retain the two extra boundedness assumptions. The
identity origin proof is the direct image witness, not a chosen lift. All field,
finite-type, separatedness, over-base and dimension hypotheses are present.
The coefficient finiteness helper wraps the already recorded proof and adds no
hypothesis beyond positivity. The only compilation corrections were wrapping
five lines over 100 characters; no mathematical mismatch was found.
