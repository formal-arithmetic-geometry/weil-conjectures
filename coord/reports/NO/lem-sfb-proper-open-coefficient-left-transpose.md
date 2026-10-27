## Worker report

The module `Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose` states
`AlgebraicGeometry.ProEtale.CondensedRing.properOpenCoefficientLeftTranspose`.
Its only postponed proof is this theorem's `sorry`. The two helper definitions
`properOpenCoefficientLeft` and `properOpenCoefficientLeftExpanded` contain the actual
composites from the node, with no choice of new functors, maps, or adjunctions.
The node is copied unchanged except for `lean`; there is no statement correction,
new node, or dependency repair.

Source read: current `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-prop-scalar-six/det-prop-scalar-six-compact-support.proof.md`, Independence paragraph,
including its restriction characterization and use of the same pullback identifications
and adjunction maps. The node's four proof steps are in the theorem docstring.

Hypothesis-by-hypothesis correspondence:

- The prime ell is `(ell : ℕ) [Fact ell.Prime]`.
- The positive-characteristic field is `(k : Type u) [Field k]`
  `[Fact (ringChar k).Prime]`; for a field this is exactly positive characteristic.
  `[Fact (ringChar k ≠ ell)]` is the prime-to-characteristic condition, with the
  inequality oriented as in the recorded direct-image declaration.
- `Z Y V : Over (Spec (.of k))` makes all named morphisms k-morphisms.
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on `Z.hom` and `Y.hom`
  render separated finite-type schemes over k. No unnecessary property of V is
  assumed: it is already an open subscheme of Y by the next binder.
- `(p : Z ⟶ Y) [IsProper p.left]` and
  `(v : V ⟶ Y) [IsOpenImmersion v.left]` are precisely p proper and v open.
- `pullback p.left v.left` is the actual scheme Z_V. Its `pullback.fst` is u;
  its `pullback.snd` is q. `pullback.condition` is used as the proof argument
  to the existing square comparison, never added as a tautological conclusion.
- `{Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')`
  `(_ha : ListedCoefficientMap ell a)` uses the exact coefficient-map predicate
  publicly imported by the recorded direct-image dependency. Its finite-ring,
  integral, field, rationalization, filtered-colimit Qbar, continuous-to-finite,
  identity and composite cases remain available. No flatness or invertibility
  hypothesis is added.
- `(M : ConstantModelConstructibleFiniteTor Λ.X Z.left)` is the full subcategory
  defined by `constantModelBoundedConstructible` intersected with
  `DerivedCategory.finiteTorAmplitude`. Thus `M.obj` is precisely the ambient
  ordinary unbounded derived object with the node's Dctf condition; there is no
  extra bound or coefficient-flatness assumption.

Objects and canonical maps:

- `scalarSixChange a S` is T_S, the existing total derived extension along
  `coefficientMap a.hom.hom S`. It is ordinary extension, without completion.
- `scalarSixPull Λ f` is L_f in the exact termwise presentation of total derived
  inverse image. `RootCoordinateFace.lower Λ.X f` is R_f, the recorded
  `moduleObjectDerivedPushforward`. Their `RootCoordinateFace.adjunction` is
  induced from the actual module adjunction. This is the same canonical
  derived pull/push calculus, not a copied definition of it.
- `(scalarDirectImagePullbackData.theta a f).inv` is c_f. Its `hom` is c_f inverse.
  The existing data is normalized by `thetaNormalization` to the canonical tensor
  comparison; the choice in the imported interface is uniquely determined there.
- `RootCoordinateFace.squareUpper Λ.X u q p v pullback.condition` is a.
  Its definition composes the canonical pullback compositors through the actual
  equality pu=vq. Replacing Λ by Λ' gives a'.
- `scalarDirectImageMate a p` is gamma. Its definition is exactly the mate of c_p
  for the recorded adjunctions, hence the adjunct of T(epsilon) c_p.
- `RootCoordinateFace.exchange Λ.X u q p v pullback.condition` is b. Its definition
  takes the mate of a for the p and q adjunctions, so its component has exactly
  the specified transpose L_u(epsilon) a. The primed exchange is used in h_L.
- P is written explicitly as `(RootCoordinateFace.lower Λ.X p.left).obj M.obj`.
  The composite a_P followed by L_u(epsilon) is written explicitly inside
  `(scalarSixChange a (pullback p.left v.left)).map` and is the node's t.

Clause-by-clause correspondence (Lean `≫` is left-to-right composition):

1. `properOpenCoefficientLeft` starts with theta_v.hom at P (c_v inverse), then
   maps gamma through L'_v, then applies the primed exchange b', and finishes
   with R'_q of theta_u.inv at M (c_u). Its source and target are exactly the
   displayed source T_V L_v P and target R'_q T_ZV L_u M of h_L.
2. The theorem's first conjunct applies L'_q to that morphism and then the q
   counit at T_ZV L_u M: this is the displayed tau(h_L), written explicitly.
   It equals `properOpenCoefficientLeftExpanded`. That definition is, in order,
   L'_q(c_v inverse), a' at T_Y P, L'_u L'_p(gamma), L'_u(epsilon'_p), c_u.
   Reversing the diagrammatic order is precisely the node's first formula.
3. The second conjunct says that this expansion equals c_q at L_v P followed
   by T_ZV of a_P then L_u(epsilon_p). It is exactly the second equality
   tau(h_L) = T_ZV(t) c_q, together with conjunct 1.
4. The third conjunct is the separately requested coherent-pullback equation:
   L'_q(c_v inverse), then a', then L'_u(c_p), then c_u at L_p P equals
   c_q at L_v P followed by T_ZV(a_P). Every occurrence of P is the same R_p M.
5. There is no `IsIso` binder for gamma or b, and neither is inverted in any term.
   Only the canonical pullback isomorphisms use `.hom`/`.inv`.

Recorded dependency declarations read and used:

- `sk-def-sfb-coefficient-change`: module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`,
  `AlgebraicGeometry.ProEtale.coefficientMap`, identity/composition and the two
  coefficient-square equations. These underlie the existing scalarSixChange.
- `sk-def-sfb-constructible`: module `Sheaf.Paper.FiniteConstantRingedLocalModel`,
  publicly retaining `AlgebraicGeometry.ProEtale.ConstantModelConstructibleFiniteTor`
  and `constantModelBoundedConstructible` from `CondensedConstantConstructibility`.
  The internal-module constructibility declaration is used, not the additional
  ringed-site local-model predicate.
- `sk-def-sfb-module-derived-pushpull`: module
  `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward` and
  `moduleObjectDerivedPullback`, with the imported derived adjunction and exact
  pullback comparison. The root-coordinate interface uses precisely these functors.
- `det-prop-scalar-six-direct-image`: module `Sheaf.SixFunctors.ScalarSixDirectImage`,
  `scalarSixDirectImage`; its public mate interface supplies
  `scalarDirectImageMate`, `scalarDirectImagePullbackData`, and
  `RootCoordinateFace.adjunction`, `squareUpper`, `exchange`. The last three
  signatures and complete definitions were read in `RootTowerCoordinateFace`.
  The counit clause of `scalarSixDirectImage` is exactly the proof's step 4.
- `det-prop-scalar-six-pullback`: module `Sheaf.SixFunctors.ScalarSixPullback`,
  `scalarSixPullback`; its public definitions supply `scalarSixPull`,
  `scalarSixChange`, `scalarSixPullComp`, `ScalarSixPullbackData.theta` and
  `.composition`. These are the prescribed comparisons, not arbitrary isomorphisms.
- `sk-def-sfb-dc-setting`: module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  the standing Over/finite-type/separated setting documented with
  `compactificationOverField`. No compactification is chosen in this calculation.
- Proof dependency `def-sfb-module-derived-pushpull-adjunction`: direct import of
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`,
  `derivedUpperStarLowerStarAdjunction`; its K-flat/K-injective signature and
  docstring, and `leftDerivedUpperStarIsoMapDerivedCategory`, were read.
- Proof dependency `lem-sfb-adjunction-transpose-square`: direct import of
  `Mathlib.CategoryTheory.Adjunction.Basic`,
  `CategoryTheory.Adjunction.homEquiv_naturality_right_square_iff`, read at lines
  270–276. It applies to arbitrary maps and does not impose invertibility.

Edge cases checked before writing: v the identity (canonical unit/compositor
calculation); p the identity (triangle identity); identity coefficient map
(the normalized comparison specializes to the unit comparison); empty V and
zero M (all formulas still type and reduce to maps between zero objects);
non-flat finite coefficient maps (no tensor-exactness premise); ell=2 with
odd characteristic; integral and filtered-colimit Qbar coefficient cases.
All schemes retain universe u, coefficient sheaves Ab.{u+1}, and the existing
small pro-etale site's object/morphism sizes; no equality of site universes or
new smallness premise is imposed. No statement fault or dispute was found.

Searches for existing declarations (actual msearch.py outputs are preserved in
sandbox searches.jsonl):

- LeanFinder query: “Inverse adjunction transpose of coefficient extension followed
  by open base change equals scalar extension of the restricted counit using
  coherent pullback comparisons”. Eight hits included
  `Scheme.Modules.restrictAdjunction_counit_app_app`,
  `SheafOfModules.PullbackConstruction.adjunction`,
  `ModuleCat.ExtendRestrictScalarsAdj.counit`, and
  `SheafOfModules.pushforwardPushforwardAdj_counit_app_val_app`.
  All are underived adjunction calculations; none states this condensed-module
  scalar/open transpose equality.
- Loogle query: `CategoryTheory.Adjunction.homEquiv_naturality_right_square_iff`.
  One exact generic hit, already the recorded Mathlib proof leaf. It does not
  give the scalar-composition calculation itself.
- msearch grep query: `homEquiv_naturality_right_square_iff|mateEquiv_counit`,
  directory CategoryTheory. Five hits, in Adjunction/Basic, Adjunction/Mates,
  Monoidal/Closed/Functor. Generic transpose and mate formulas only.
- LeanSearch query: “The inverse transpose of scalar coefficient change followed
  by open base change is the coherent pullback comparison followed by scalar
  extension of the counit”. Eight hits, including
  `ModuleCat.ExtendRestrictScalarsAdj.homEquiv_symm_apply`,
  `Scheme.Modules.pseudofunctor_mapComp_inv_τl`, and
  `ModuleCat.RestrictionCoextensionAdj.counit'`; none states this result.
- rg in the project's `lean/WeilConjectures` and `lean/Sheaf` for
  `properOpenCoefficientLeft|left.*[Tt]ranspose|transpose.*coefficient`
  found unrelated finite constant-ring projection/adjunction results and
  semilinear-system results, not this ordinary condensed-module calculation.
  Exact search for the node id in `lean/WeilConjectures` found no declaration.
- Exact new-name search for `properOpenCoefficientLeft` in Mathlib,
  `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf`
  found no collision. Existing neighboring proper/open results on constant
  finite etale coefficients have different categories and different maps;
  `RootCoordinateFace.exchange` and `scalarDirectImageMate` are reused instead.

Validation: scompile.py compiled both sandbox and library-module forms cleanly
under the default 60-second limit (7.8 s and 8.4 s); no warnings were emitted.
The sole elaboration repair was using `pullback.condition` with its implicit
morphism arguments. No mathematical statement or interface was changed.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
