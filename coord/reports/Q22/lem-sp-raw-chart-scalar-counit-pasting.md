## Worker report

The module `Sheaf.Paper.RawChartScalarCounitPasting` states the node as
`AlgebraicGeometry.Etale.rawChartScalarCounitPasting`, with one postponed theorem
and four real helper constructions belonging to this same raw chart. No new DAG
node, dependency repair, or statement correction is needed.

Source read: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md`, Charts. It specifies summation followed
by ordered projective-line integration, with the canonical scalar identification
of the explicit twisted shifted pullback. The item's four proof steps are included
in the theorem docstring, with all cited ingredients.

Hypotheses and clauses, in the order of the node:

- A field k of characteristic p>0, a prime ell distinct from p: `ell p : ℕ`,
  `[Fact ell.Prime]`, `_hp : 0 < p`, `_hEll : p ≠ ell`, `k : Type u`, `[Field k]`,
  `[CharP k p]`. A field of positive characteristic automatically has prime
  characteristic; no additional primality assumption on p is imposed.
- Finite commutative unital rings and their unital map: `{A B : Type (u + 1)}`,
  `[CommRing A] [CommRing B] [Finite A] [Finite B]`, `φ : A →+* B`.
  The common N is `ell ^ n`, with `hA`, `hB` its vanishing in the two rings.
  Positivity of N is the explicit term `pow_pos (Fact.out : ell.Prime).pos n`.
- U and Y are separated finite-type k-schemes: `U.Over`, `Y.Over`, and for each
  structure map `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`. The affine
  space V is the dependency's canonical ordered coordinate model
  `affineTraceTower Y d`; `affineTraceProjection Y d` is p_d. This includes its
  literal identity at d=0 and is canonically the ordered polynomial affine space.
- d≥0 is `d : ℕ`. The chart is `e : U ⟶ affineTraceTower Y d`, with `[Etale e]`,
  `[IsSeparated e]`, `[LocallyOfFiniteType e]`, `[QuasiCompact e]`.
  Its k-morphism condition is `_he : e ≫ affineTraceProjection Y d ≫
  (Y ↘ Spec (.of k)) = (U ↘ Spec (.of k))`. This is the usual structure-map
  equation, and does not require choosing a further k-structure on V.
- The ordinary etale category is `DerivedCategoryModule R T`. Its bounded
  constructible finite-Tor full subcategory is the recorded predicate
  `ProEtale.AdjunctionTransfer.etaleProperty R T`: bounded constructible cohomology
  intersected with `DerivedCategory.finiteTorAmplitude` against every degree-zero
  module sheaf. Equations in the ambient category are the same equations in its
  full subcategory. The node works on this site; its pro-etale introductory
  notation adds no pro-etale conclusion to this particular statement.
- T_T is the already published `Etale.scalarExtension φ T`, the derived extension
  with its B-action. It is used at all three schemes; no new tensor is defined.
- E_R is `(etaleLowerShriek (ModuleCat R) e inferInstance).mapDerivedCategory`;
  h_R is `(upperStar (ModuleCat R) e).mapDerivedCategory`; v_R is exactly
  `derivedEtaleLowerShriekUpperStarAdjunction ... .counit`.
- P_R is `rightDerivedLowerShriekOfCompactification (ModuleCat R) c`, for the
  explicitly bound compactification c of p_d. Quantification over c allows the
  chosen compactification of the node. G_R is the published ordered
  `affineTraceRight R N hR Y d`, the model of p_d^*(-)(d)[2d]. Its finite Tate line
  and shifts are the published `ordinaryFiniteLine` and shifted tensor factors.
- u_R is `affineScalarCompactificationCounit`, the specified ordered affine
  counit transported along `reductionEtaleAffineLeftIso` to P_R. Its only technical
  data, Noetherianity of Y and invertibility of N on Y, are conclusions
  `∃ hNoeth hY`, not additional hypotheses. Both follow from the setting.
- `rawChartRight` is G_R followed by exact h_R. `rawChartCounit` is literally
  `P_R.map (v_R.app (G_R.obj K)) ≫ u_R(K)`, hence precisely w_R in Lean's
  left-to-right composition convention. It does not use a compact-support
  comparison for p_d e.
- beta_d is `etaleCoefficientMap φ c`; sigma_e is `(sumCoefficientIso φ e).hom`.
  `rawChartLeftScalarMap φ d e c M` is literally beta_d(E_A M), followed by P_B
  applied to sigma_e(M); this is s_M with the prescribed order.
- a_d is `reductionEtaleAffineScalarIso ... K`, and a_e is
  `(properOpenCoefficientPullbackIso φ e).inv.app`. The canonical a_K is
  `rawChartScalarIso ... K`: the published `reductionEtaleChartScalarIso` between
  the explicit derived-pullback chart functors, transported at both endpoints
  using `leftDerivedUpperStarIsoMapDerivedCategory`. All these are actual
  isomorphisms. No arbitrary comparison or counit-defined map is supplied.
- The first conjunction is exactly the factorization
  `rawChartScalarIso.hom = a_e(G_A K) ≫ h_B.map a_d.hom`, for every ctf K.
- The second is exactly
  `s(h_A G_A K) ≫ P_B.map (E_B.map a_K) ≫ w_B(T_Y K) = T_Y.map w_A(K)`.
  The source and target are precisely those of the node's composite equation.
- The remaining eleven conjunctions give preservation of the stated full
  subcategories by G, h, E and P separately for R=A,B, and by T at Y,V,U.
  Composing these implications gives membership of every intermediate object
  in s, a and w, including every scalar extension in the formula. These are
  the node's stated functor restrictions, rather than assumptions supplied by
  the caller or preservation only on an unspecified class of objects.
- The ring map is arbitrary: there is no flatness, projective-dimension,
  injectivity, surjectivity or nontriviality hypothesis. The affine integration
  order and the actual sum counit are fixed by the definitions used above.

Dependency declarations read and used (including transitive presentation helpers):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `ProEtale.CondensedRing.compactificationOverField`, and
  `WeilConjectures.Compactification.Over`: compactifications in the standing
  finite-type separated field setting. No new setting predicate is introduced.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule` and the ordinary derived cohomology convention.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`; and
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`:
  `Scheme.HasFixedCoefficientProEtaleTorAmplitude`. These retain the node's
  introductory pro-etale notions; no private constructibility or Tor predicate
  is defined in this delivery.
- `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`:
  `ProEtale.AdjunctionTransfer.etaleProperty` and `proEtaleProperty`.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`:
  `ProEtale.scalarExtensionFunctor`; and
  `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.OrdinaryDerivedChangeOfRings` and the retained ringed-site cochain
  model. The ordinary etale specialization actually used is
  `Etale.scalarExtension` in `Sheaf.Paper.EtaleDerivedScalarTensor`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`:
  `Scheme.finiteEtaleTateLine`, `Scheme.finiteEtaleTateTwist`.
- `Sheaf.Paper.EtaleSumCounitScalar`: `Etale.etaleSumCounitScalar`;
  `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`:
  `ProEtale.CoefficientCompatibility.sumCoefficientIso`, `etaleCoefficientMap`;
  `Sheaf.Paper.ProperOpenCoefficientRefinement`:
  `Etale.properOpenCoefficientPullbackIso`.
- `Sheaf.Paper.AffineCounitScalar`:
  `Etale.affineScalarCompactificationCounit`, `Etale.affine_counit_scalar`;
  its public import `Sheaf.SecSmoothPurity.ReductionExceptional`:
  `ProEtale.reductionEtaleAffineScalarIso`, `reductionEtaleChartScalarIso`.
- `Sheaf.Paper.EtaleCtfChartDomain`:
  `ProEtale.AdjunctionTransfer.etaleCtfChartDomain`, `etaleCtfChartScalarDomain`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  canonical comparisons are characterized on flat-term K-flat representatives,
  not selected as arbitrary isomorphisms.
- Proof imports: `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`
  (`Etale.nonempty_etaleCompactSupportNormalization`);
  `Mathlib.AlgebraicGeometry.Noetherian` (finite type over a field is Noetherian);
  `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
  (`CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`);
  `Sheaf.Paper.FiniteTateBalancedScalarPullback`
  (`Etale.finiteTateBalancedScalarPullback`);
  `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
  (`Scheme.etaleFiniteTwistPullback`);
  `Sheaf.Paper.CochainPullbackTensorShift`
  (`CategoryTheory.CochainPullback.tensorComparison_commShift`).

Edge cases checked before writing and again against the final signature:

- d=0 is included; the published affine tower, scalar comparison and adjunction
  are the identity, leaving exactly the sum-counit scalar equation.
- e=id retains the actual sum counit and its canonical pullback comparison;
  φ=id retains the unit comparisons. Neither case is silently excluded.
- Empty U, empty Y and zero input complexes are included by the ambient categories
  and the preservation clauses; no nonemptiness assumption occurs.
- n=0 gives N=1 and forces both coefficient rings to be zero rings. `[CommRing]`
  permits these, and the unit and roots-tensor constructions still exist.
- Nonflat maps such as Z/ell^2 to Z/ell are permitted. Every tensor is derived;
  the finite-Tor domain is a property of the input/output over its own ring,
  not a finite-projective-dimension assumption on B as an A-module.
- Universe u is explicit throughout; the site is Scheme.{u} and coefficients and
  module values are Type (u+1), exactly the dependency presentation. No site
  object/Hom universe equality is introduced.

Searches for a pre-existing full statement:

1. msearch.py leanfinder: `Derived scalar extension preserves the composite counit
   of etale sum extension and ordered affine integration`. Eight results concern
   algebraic cotangent maps and composition of etale algebras; no full match.
2. msearch.py loogle: `CategoryTheory.Adjunction.comp_counit_app`. One match,
   Mathlib.CategoryTheory.Adjunction.Basic. Read its exact signature: it only
   expands a composite counit, and does not assert the specified scalar equation
   or right comparison factorization.
3. msearch.py grep: `comp_counit_app|rawChart.*Scalar|raw_chart.*scalar` in
   CategoryTheory. Eleven hits: the general composite counit formula and uses
   in mates, shift and monoidal functor code; no geometric scalar equation.
4. msearch.py leansearch: `Scalar extension commutes with the composite counit of
   etale sum extension followed by affine space integration`. Eight hits on
   ordinary extension/restriction counits and algebraic scalar maps; no match.
5. rg of `lean/WeilConjectures` for raw/chart scalar names and composite counits,
   and search for the exact blueprint id: no exact item declaration. Generic
   composite counit lemmas do not give these specified geometric comparisons.
6. rg of `lean/Sheaf` for raw chart, chart scalar and scalar counit declarations:
   found and reused `reductionEtaleChartScalarIso` and the two separate counit
   lemmas; no theorem combines the canonical right factorization with this raw
   scalar counit equation and the finite-Tor domains.
7. Exact names `rawChartRight`, `rawChartScalarIso`, `rawChartLeftScalarMap`,
   `rawChartCounit`, `rawChartScalarCounitPasting` searched in Mathlib, both project
   roots and `dag/lean_names_upstream.json`: no conflicts.

No STATEMENT-DISPUTED flag and no node faults. The first compiler pass exposed a
missing inferred `Over` instance for the iterated affine tower: the k-morphism
hypothesis is now written as its equivalent explicit structure-map equality.
The next pass compiled both module modes; its sole long-line warning was wrapped.
Final compilation and delivery preflight are recorded by the prescribed wrappers.

## Second reading by Q22

Reread the node and the final module separately after writing. This is the same
worker's rereading: the dispatch brief prohibits starting other agents and assigns
independent delivery review to the maintainer; no independent reviewer is claimed.

The positive-characteristic field and distinct prime match all four binders.
The rings, common annihilating power and arbitrary unital map match the finite
CommRing binders without flatness. The separated finite-type source and base,
the ordered affine tower, and the explicit k-morphism equation match the geometry.
The first attempted IsOver binder needed a missing tower instance; expressing its
actual equality repaired elaboration without adding data or changing the node.
The raw right functor uses exact inverse image and the published ordered G,
while its scalar comparison transports the existing canonical derived comparison
at both endpoints. Checking these endpoints against `properOpenCoefficientPullbackIso`
confirms that the factorization uses its inverse, not its forward map.
The left scalar arrow starts with beta(E M), then P_B(sigma M). The raw counit
starts with P_R(v_R(G_R K)), then the affine u_R. Thus the second equation has
precisely the orientation and all three factors requested. Checking the eleven
preservation clauses gives every successive input and scalar-extended intermediate
in the formula in Dctf, not merely bounded-below membership. No clause for a
compact-support comparison of p_d e has been introduced. The theorem is the only
postponed declaration, and all four helper definitions have actual data. The
only formatting defect found was one long line, now wrapped. No mathematical
mismatch or statement correction was found.
