## Worker report

Item: `lem-sfb-proper-open-coefficient-right-transpose`.
Module: `Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose`.
Namespace: `AlgebraicGeometry.ProEtale.CondensedRing`.

The module states `properOpenCoefficientRightTranspose_eq` with `sorry` as its whole proof.
It adds two real composite-map definitions belonging to this node:
`properOpenCoefficientRightMap` is h_R, and `properOpenCoefficientRightTranspose` is tau(h_R).
Neither definition contains a postponed proof or a choice. The canonical coefficient
comparison, exchange, square compositor and derived functors are reused, not redefined.
No node correction, new node or dependency repair is required. Only the item's `lean`
record changes.

Hypotheses and objects, in order:

- The prime ell is `(ell : ℕ) [Fact ell.Prime]`. The field is `(k : Type u) [Field k]`.
  `[Fact (ringChar k).Prime]` expresses positive characteristic p_0; the characteristic
  of a field, when positive, is prime. `[Fact (ringChar k ≠ ell)]` is ell ≠ p_0.
- `{Z Y V : Over (Spec (.of k))}` makes all schemes and arrows k-linear.
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on each of Z.hom and Y.hom
  express precisely the separated finite-type assumptions. The open V is supplied by
  `(v : V ⟶ Y) [IsOpenImmersion v.left]`; its finite type and separation follow from the
  Noetherian finite-type target, so they are not additional assumptions.
- `(p : Z ⟶ Y) [IsProper p.left]` is the specified proper morphism.
  `pullback p.left v.left` is the actual Z_V. Its u and q are respectively
  `pullback.fst p.left v.left` and `pullback.snd p.left v.left`.
  `pullback.condition` is u ≫ p = q ≫ v.
- `{Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')` uses bundled commutative condensed rings.
  `(_ha : ListedCoefficientMap ell a)` is exactly the direct-image dependency's listed
  coefficient maps, including finite composites and the filtered-colimit convention
  for the algebraic closure. It imposes no flatness.
- `M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z.left)` is the
  ordinary unbounded module-derived object. `_hM` is the conjunction of
  `constantModelBoundedConstructible Λ.X Z.left M` and
  `DerivedCategory.finiteTorAmplitude _ M`, exactly membership in Dctf.
- T_S is `scalarSixChange a S`. L_f is `scalarSixPull Λ f`, definitionally the
  same exact-pullback localization as `RootCoordinateFace.upper Λ.X f`.
  R_f is `RootCoordinateFace.lower Λ.X f`, exactly
  `moduleObjectDerivedPushforward Λ.X f`, the total right derived module direct image.
  Replacing Λ by Λ' supplies the primed functors.
- Units/counits come from `RootCoordinateFace.adjunction`; this is the recorded
  exact-pullback/total-derived-direct-image adjunction. Exactness identifies this L_f
  with total left derived pullback, as in `leftDerivedUpperStarIsoMapDerivedCategory`.
- c_f is `(scalarDirectImagePullbackData.theta a f).inv`; its thetaNormalization
  fixes the canonical non-flat scalar/pullback comparison. No arbitrary isomorphism
  is quantified over. The adjunction/counit normalization is exactly that used in
  the recorded direct-image theorem.
- a is `RootCoordinateFace.squareUpper Λ.X u q p v pullback.condition`, the composite
  of inverse `upperComp` for q,v, transport of the commuting scheme maps, and
  `upperComp` for u,p. Using Λ' gives a'. The primed exchange is likewise obtained
  by Λ' substitution. They are setup notation and not additional conclusions.
- b is the existing `(RootCoordinateFace.exchange Λ.X u q p v pullback.condition).app M`.
  Its mate definition and `exchange_adjuncts` identify it with the stated adjunct of
  `squareUpper.hom.app ((lower Λ.X p).obj M) ≫ upper(u).map (adjunction(p).counit.app M)`.
  This last expression is precisely t, with P = `(lower Λ.X p).obj M`.
- gamma is `(scalarDirectImageMate a q).app ((scalarSixPull Λ u).obj M)`, the mate
  of inverse theta under the same adjunctions. `properOpenCoefficientRightMap`
  defines h_R as T_V(b) followed by gamma. `properOpenCoefficientRightTranspose`
  defines tau(h_R) as L'_q(h_R) followed by the primed counit at T_(Z_V)(L_u M).

Conclusions, in order (Lean's `≫` reads left to right):

1. The first conjunct is tau(h_R) = L'_q(T_V(b)) ≫ c_(q,R_q L_u M) ≫ T_(Z_V)(epsilon_q).
   This is the first displayed expression in the node, in Lean's composition order.
2. The second conjunct is tau(h_R) = c_(q,L_v P) ≫ T_(Z_V)(L_q(b) ≫ epsilon_q).
   This is the second displayed expression.
3. The third conjunct is tau(h_R) = c_(q,L_v P) ≫ T_(Z_V)(a_P ≫ L_u(epsilon_p)).
   This is the final expression T(t) composed after c, retaining the specified a_P.
4. The last conjunct is L_q(b) ≫ epsilon_q = a_P ≫ L_u(epsilon_p), the exchange
   counit identity. The symbol t is expanded, so no tautological equality is added.

Together, the first three equalities express exactly the node's chain. None assumes
invertibility of b or gamma. All equalities are morphism equalities in the actual derived
category, rather than cohomology-level isomorphisms.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `AlgebraicGeometry.ProEtale.coefficientMap` and its naturality identities; used through
  `scalarSixChange` and the normalized pullback comparison.
- `Sheaf.Paper.FiniteConstantRingedLocalModel`, publicly retaining
  `Sheaf.Paper.CondensedConstantConstructibility`: `constantModelBoundedConstructible`
  and `ConstantModelConstructibleFiniteTor` (the latter's predicate is expanded).
  The newer ringed-site helper is not needed for internal module objects.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: `moduleObjectDerivedPushforward` and
  `moduleObjectDerivedPullback`; its public upstream module supplies
  `derivedUpperStarLowerStarAdjunction` and `leftDerivedUpperStarIsoMapDerivedCategory`.
- `Sheaf.SixFunctors.ScalarSixDirectImage`: `scalarSixDirectImage`, with the public
  `ScalarDirectImageMateCoherence` interface: `scalarDirectImageMate` and
  `scalarDirectImagePullbackData`.
- `Sheaf.SixFunctors.ScalarSixPullback`: `scalarSixPullback`, together with its public
  `ScalarSixDefinitions`: `scalarSixChange`, `scalarSixPull`, `ScalarSixPullbackData.theta`
  and its normalization. These are the dependency's specified canonical maps.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `compactificationOverField` and the Over-field setting (no compactification is needed
  in the calculation itself).
- `Sheaf.Paper.RootTowerCoordinateFace` (publicly supplied by direct-image coherence):
  `upper`, `lower`, `adjunction`, `upperComp`, `squareUpper`, `exchange`,
  `exchange_adjuncts`. The latter was read to check the specified counit normalization;
  no duplicate exchange or compositor was introduced.
- Proof dependency `lem-weil-pbc-adjunction-of-natural-bijection` is a Mathlib leaf:
  `CategoryTheory.Adjunction.mkOfHomEquiv` and `homEquiv_counit` in
  `Mathlib.CategoryTheory.Adjunction.Basic`. Its full CoreHomEquiv and inverse formula
  were read. This module is imported explicitly as a proof dependency.

Sources checked: current blueprint compact-support proof, Independence paragraph;
current scalar direct-image and pullback declarations; Stacks categories.tex,
Tag 0037 (`definition-adjoint`) and its following equivalence of the adjunct formulas.

Edge cases checked before writing: M = 0; V empty (and hence Z_V empty); p or v an
identity; identity coefficients; non-flat finite listed maps such as Z/ell² → F_ell.
The argument is the adjunct inverse identity and naturality and applies in each case.
There is no nonempty, nonzero, flatness, proper-exchange invertibility, gamma invertibility,
completion, or extra universe equality assumption. The site/coefficients retain the
published u/u+1 sizes. No STATEMENT-DISPUTED issue was found.

Searches (all through the prescribed wrapper or read-only source searches):

- msearch leanfinder: "The inverse adjoint transpose of coefficient change of a base
  change map followed by the direct image coefficient mate is scalar extension of the
  exchange counit". Eight hits: generic IsBaseChange linear algebra and underived
  ModuleCat extension/restriction formulas. None states this derived exchange chain.
- msearch loogle: `CategoryTheory.Adjunction.homEquiv_counit`. One exact generic inverse
  transpose formula, used through the existing Mathlib proof-dependency node.
- msearch grep: `homEquiv_counit|homEquiv_naturality_left_symm` in
  `CategoryTheory/Adjunction`. 21 hits, generic adjunction APIs; no full chain.
- msearch leansearch: "Adjunction inverse transpose of a composite equals left adjoint
  of the composite followed by counit". Eight generic adjunction hits including
  `homEquiv_symm_apply`, `comp_counit` and `comp_counit_app`; no item-equivalent theorem.
- rg over `lean/WeilConjectures` and `lean/Sheaf`: proper/open, right-transpose, scalar
  exchange names and the node ID. Found the different finite/etale proper-open
  coefficient mate module and the canonical RootCoordinateFace exchange interface.
  Neither gives this statement for listed condensed coefficients on these categories.
  Exact new declaration names have no existing match. The prescribed upstream ID
  search likewise returned no declaration.

Validation: scompile.py compiled the sandbox and actual library module without errors
or warnings other than permitted sorry usage. The library-mode check took 10.6 seconds.
Every delivered file starts with `module`; `autoImplicit` is false; every variable and
universe is explicitly bound. All lines are at most 100 characters.

## Second reading by NP

I reread the node and the final source after compilation, matching all binders and four
conjuncts above. This is a separate self-check; no second worker was started because the
dispatcher brief explicitly forbids starting agents. The maintainer's independent review
remains separate. In particular I checked that fst is u, snd is q; that squareUpper has
orientation L_q L_v → L_u L_p; that inverse theta is c; that the counit at L_u M is q's,
whereas the counit inside t is p's; and that the objects in the two c components are
R_q L_u M and L_v R_p M respectively. I checked that the first three conjuncts share
tau(h_R), which is equivalent to the displayed chain, and that the fourth retains a_P.
No mismatch or source correction was found. Helpers define only the node's h_R and its
inverse transpose, with real data; the sole theorem remains sorry as stage 2 requires.
