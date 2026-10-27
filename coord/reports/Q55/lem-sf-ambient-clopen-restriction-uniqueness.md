## Worker report

The module `Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness` states
`AlgebraicGeometry.ProEtale.AmbientClopenRestriction.ambientClopenRestrictionUniqueness`.
The only postponed proof is that theorem; all helpers have actual data. No node statement
is corrected, and there is no disputed statement. The additional statement dependencies
are existing, landed definition nodes used explicitly, including
`def-pur-clopen-test-piece-inclusion`, which owns `Scheme.ProEt.clopenTestPiece`.
The theorem `lem-pur-clopen-ringed-module-gluing` remains in `proof_deps` only;
its conclusion is not used to construct any part of this statement. Their transitive dependency graphs were
checked for a path back to this item: none was found.

Hypothesis and clause correspondence, read against the whole node:

* The algebraic closure of the finite field is `K : WeilConjectures.FiniteFieldDatum`;
  `K.p`, `K.q`, `K.k₀`, `K.k` retain the prime, prime power, finite field and closure.
  `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ K.p` express the distinct coefficient prime.
  `E`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` are the
  specified finite extension. `scalarRings l E n` is only `ULift` of the recorded
  quotient `Padic.coefficientExtensionRing l E (n+1)`, with the recorded quotient
  maps `scalarTransitions`. Thus all positive levels, starting with A₁, occur.
* `U V W Z : Over (Spec (.of K.k))` and the four pairs of
  `[LocallyOfFiniteType _.hom] [QuasiCompact _.hom]` give precisely finite-type
  k-schemes and morphisms over k. There is no separatedness assumption on these
  structure morphisms. The four `Over` arrows have underlying maps `.left`.
* `[IsOpenImmersion k.left]`, `[IsOpenImmersion i.left]` and their `QuasiCompact`
  instances give the two quasi-compact opens. `[IsProper r.left] [IsProper p.left]`
  are exactly properness. `h` is the equality of the two composites. No pullback
  hypothesis on this original square occurs.
* `pullback p.left i.left` is V_W, its `fst` is b, its `snd` is q, and the published
  `StrictTower.squareLift` is literally `pullback.lift k.left r.left h`, namely s.
  The first five conclusions assert b open, q separated, and s open, proper, closed.
  The following locally-finite-type and quasi-compact conclusions assert V_W finite
  type over the original base, using `pullback.snd ... ≫ W.hom`.
* `∀ m : Option ℕ` covers either coefficient category. `some n` selects only A_(n+1)
  module sheaves, not constant towers; `none` selects `VaryingRing.Modules`, literally
  the already defined modules on the ringed vertical sequence site. It is not a
  category of diagrams in derived categories and has no cartesianness assumption.
  The node's ordinary unbounded derived categories and adjunctions are the imported
  contextual operations; this theorem's conclusions are all abelian assertions.
* `Assertion` begins with an open `C` whose inclusion range is precisely the
  complement of the range of s. Since s is the actual clopen immersion, this gives
  the scheme decomposition V_W=s(U)⊔C with the induced open scheme structures.
* The equivalence `e` has functor equal to `(pull s).prod' (pull C.ι)`, so it is
  restriction, rather than an arbitrary equivalent category. Its functor and inverse
  preserve finite limits and colimits, recording exactness.
* `σ` identifies every section of `e.inverse.obj (F_U,F_C)` with the product of
  sections on the two actual pulled-back test schemes `clopenTestPiece s T` and
  `clopenTestPiece C.ι T`. It is an additive equivalence. The next equations state
  compatibility with the actual coefficient-section action (`act`,
  `scalarRestriction`), test-object restriction maps, and componentwise module
  morphisms. The final equation states precisely the product of the two semilinear
  adjacent transitions. The finite case uses identity transitions on a repeated
  fixed category; the system case uses the horizontal restriction of the actual
  sequence-site module presheaf. Keeping the same underlying additive sections and
  the displayed scalar-action equation also expresses compatibility with restriction
  of scalars, which changes only that action. No flatness is imposed.
* The invertible s-open unit identifies the first component of `s_!G` with G;
  `IsZero` of its C-restriction gives its second component zero. Thus its image
  under the specified restriction equivalence is (G,0), up to the canonical unit.
* The natural transformation `π` has s-restriction exactly the s-open unit on s*F
  and C-restriction zero. After the preceding unit identification this is (1,0).
  These equations uniquely characterize the canonical projector since e is faithful.
  It is a morphism of actual systems, including their transitions.
* The b-open and k-open units are isomorphisms. `H F G` is an `Equiv` between the
  exact two Hom sets in the node. Its forward-map equation says that composing its
  value with the k-open unit equals applying k* to the original map after
  `restrictionSource`. That source map is explicitly s* of the b-open unit,
  inverse pullback compositor, and the equality s b=k. Hence this is restriction
  followed by the inverse identity open unit, not an arbitrary Hom equivalence.
  The next equation is naturality, contravariantly in F and covariantly in G.
  The separately recorded implication for any a,b is restriction uniqueness.
* `β` is a natural isomorphism from p*i_! to b_!q*. Its inverse's displayed
  open-unit equation makes it exactly the b-open adjunct of q* of the i-open
  unit, followed by the canonical pullback compositor. The whole preceding Hom
  assertion quantifies over arbitrary F, so instantiating F=q*M gives the last
  clause for every M. No evaluation of derived morphisms or faithfulness of such
  evaluation is used or asserted.

Dependency declarations read and used:

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting the actual coefficient-ring,
  uniformizer, integer-ring and transition constructions of `CoefficientExtension`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`;
  objects are weakly etale morphisms, with object universe u+1 and Hom universe u.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`. The latter's existing section modules,
  morphisms and abelian structure are inherited by the coefficient dispatchers.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; ordinary localization, never a completed/localized subcategory.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the recorded
  `Scheme.proEtaleConstantRingDerivedPullback`, and reexported actual
  `proEtaleRingModules`, `proEtaleRingModulePullback`, module/direct-image and
  canonical derived adjunction operations. StrictTower is their constant-ring
  specialization with its section-normalized constant-ring comparison.
* `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections` and
  `SemilinearDerivedSectionsData`, with actual `Systems`, `DS` and `evaluation`
  from the publicly imported `SemilinearSystemModels`. VaryingRing uses precisely
  those simultaneous categories and operations, before evaluation or total limit.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` keeps underlying sections and restricts the action.
* `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `localizedSystemExtension`, `localizedSystemRestriction`, `localizedSystemExact`,
  `localizedSystemAdjunction`, retaining the actual sheafified extension and the
  normalized unit; the ordinary scheme specializations are the published wrappers.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`, `pullback.lift_fst`.
* `Sheaf.SixFunctors.OpenTensorNormalization`: `SheafOfModules.openTensorNormalization`,
  with both ordinary and systems assertions and the open-unit-normalized beta.
* Existing landed helpers explicitly used: `FiniteFieldDatum` from `FiniteFieldFiber`;
  `scalarRings`, `scalarTransitions` from `IntegralSystemCanonicalBridge`;
  `StrictTower.Modules`, `coefficients`, `modulePullback`, `moduleGComp` from
  `StrictConstantTowerOperations`; `moduleJ`, `moduleJAdj` from
  `StrictTowerOpenExtension`; `squareLift` and its clopen instances from
  `StrictTowerProperOpenArrows`; `VaryingRing.Modules`, `pull`, `extension`,
  `moduleJAdj`, `moduleGComp`, `eval` from `VaryingRingOperations` (publicly
  reexported by `VaryingRingProperOpenArrows`); `Scheme.ProEt.clopenTestPiece`
  from `ProEtaleClopenRingedModuleGluing`, owned by the existing definition node
  `def-pur-clopen-test-piece-inclusion`. Its body is the actual
  `MorphismProperty.Over.pullback` test object, not a choice from the gluing theorem.
* All already-recorded proof-dependency modules are imported as the proof plan:
  clopen module gluing; intrinsic extension by zero; module sheafification restriction;
  weakly-etale localization; proper monomorphism criterion; proper/base-change and
  proper-to-separated geometry. Mathlib `Adjunction.comp` and
  `unit_conjugateEquiv_symm` are available through the public operation imports.

Sources read: the full node including eight proof steps and review note; Stacks
`more-etale.tex` lemma-shriek-proper-and-open (0F7B), and `sites.tex`
lemma-mapping-property-glue (04TS). The former is the geometric/proper-open input;
the abelian pro-etale clopen formulation is explicitly agent-written in the node.

Edge cases checked before writing and reread against the binders: U empty (all maps
into its zero extension are unique); W empty (U and V_W empty); C empty (s is an
isomorphism, no nonempty C required); Cartesian original square (s is the canonical
isomorphism); n=0 represents A₁, not A₀; arbitrary zero or non-surjective transitions
of the module systems; zero modules; nonseparated finite-type ambient schemes.
All occur without added hypotheses. Universes retain the small pro-etale object's
u+1 and morphism's u, with u+1 modules; no site-universe equality is imposed.

Searches actually run:

* msearch leanfinder: “Clopen factorization of a proper open square gives equivalence
  of module sheaves with product and restriction Hom bijection for extension by zero”.
  Eight hits include sheaf free-module/sheafification facts, no whole statement.
* msearch loogle: “SheafOfModules, IsOpenImmersion, IsProper”. Zero hits, with
  “unknown identifier IsOpenImmersion”; this query did not establish nonexistence.
* msearch grep: `clopen|isProductOfDisjoint`, CategoryTheory: zero hits.
* msearch leansearch: “module sheaves on disjoint open components product category
  restriction equivalence extension by zero Hom restriction bijection”. Eight hits:
  `TopCat.Sheaf.isProductOfDisjoint`, its congruence lemma, four sheafification Hom
  equivalences, a sheafification composition lemma, and a topological sheaf product
  restriction formula. None is the pro-etale semilinear Hom assertion here.
* Direct rg of `clopen|Clopen` in project `WeilConjectures` and `Sheaf`, and the
  node-id grep in `WeilConjectures`: found the related existing clopen geometry,
  exact-derived comparison and system pasting APIs, not this entire statement.
  Those APIs were opened and reused, including the ordinary rather than derived
  operations. No fresh independent mathematical notion or dependency repair is needed.

Compilation uses only scompile.py, each attempt under the original 60-second limit.
Initial diagnostics exposed private-import visibility, the nonexistent shorthand
`FiniteType`, and a transition helper type/parenthesis issue; these were repaired
using public imports, the actual finite-type pair, and the typed section dispatcher.

Final scompile result: exit 0, sandbox and named library module both clean, no errors
or non-sorry warnings. The scalar-action dispatcher was made explicit with the original
`ModuleCat` scalar-action instance; no additional mathematical hypothesis was needed.

## Second reading by Q55

Read the retained node and the full module again for the repair of returned head
`8b505d55042b`, and compared the saved node with current main: only `lean` and
`stmt_deps` differ. The saved delivery log identifies that returned head. The initial
saved-packet dry run passed preflight and compilation before this metadata repair.
The following table records the second reading against each hypothesis and clause.
Here `s` means the actual `StrictTower.squareLift k.left r.left p.left i.left h`,
`b` and `q` mean the actual pullback projections; abbreviations in this table do
not introduce additional Lean declarations.

| Node hypothesis or clause | Lean rendering checked | Finding |
| --- | --- | --- |
| Algebraic closure of a finite field; prime ℓ distinct from the characteristic | `K : WeilConjectures.FiniteFieldDatum.{u}`, `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ K.p` | Same finite-field datum and distinct prime. |
| Finite extension E/ℚ_ℓ, its valuation ring, uniformizer and positive quotients | `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`; recorded `scalarRings l E n` and `scalarTransitions l E` | The coefficient construction is reused; index zero means A₁. |
| Finite-type k-schemes, without separated structure maps | `U V W Z : Over (Spec (.of K.k))`; `LocallyOfFiniteType` and `QuasiCompact` for each structure map | All four finite-type hypotheses present; no separatedness added. |
| Small pro-etale sites | `X.ProEt` in `sections`, `ringSections`, and the section formula | Actual small-site objects and their existing topology. |
| Fixed-level modules or simultaneous semilinear systems with compatible morphisms | `Modules l E (some n) X = StrictTower.Modules ... X`; `Modules l E none X = VaryingRing.Modules ... X` | Same two abelian categories; no Cartesian-system restriction. |
| Ordinary unbounded derived context and specified exact operations/adjunctions | Published operation imports; `pull`, `extension`, `openAdj`, `pullComp` dispatch to `StrictTower` and `VaryingRing` | Uses the recorded operations; conclusions stay in the abelian categories. |
| Two quasi-compact open immersions | `[IsOpenImmersion k.left] [IsOpenImmersion i.left] [QuasiCompact k.left] [QuasiCompact i.left]` | Both opens and both quasi-compactness hypotheses. |
| Proper r,p and commuting square, without a Cartesian hypothesis | `[IsProper r.left] [IsProper p.left]`; `h : k.left ≫ p.left = r.left ≫ i.left` | Exactly the stated proper/open square. |
| V_W, b,q and induced s | `pullback p.left i.left`, `pullback.fst`, `pullback.snd`, `StrictTower.squareLift` | `squareLift` is the actual `pullback.lift`, not an arbitrary map. |
| b open; q separated; s open, proper and closed | First five theorem conjuncts | Each geometric conclusion is present with the specified arrow. |
| V_W finite type over k | `LocallyOfFiniteType (pullback.snd ... ≫ W.hom)` and corresponding `QuasiCompact` | Both parts of finite type over the original base. |
| Complement C and disjoint-open decomposition | `∃ C : (pullback p i).Opens`, `Set.range C.ι = (Set.range s)ᶜ` | The actual complementary open, including empty cases. |
| Restriction equivalence for either category | `∀ m : Option ℕ, Assertion ...`; `e.functor = (pull ... s).prod' (pull ... C.ι)` | The functor is fixed to restriction. |
| Exactness of restriction and gluing | `PreservesFiniteLimits` and `PreservesFiniteColimits` for both `e.functor` and `e.inverse` | Both directions are exact. |
| Inverse sections F_U(T×U) × F_C(T×C) | Additive equivalence `σ F n T` with factors evaluated on `Scheme.ProEt.clopenTestPiece s T` and `... C.ι T` | Literal pulled-back test objects; existing definition node owns them. |
| Section formula respects coefficients and scalar restriction | First equation after `σ`, using `act` and `scalarRestriction` | Actual restricted coefficient-section actions, with unchanged underlying additive sections. |
| Section restrictions and componentwise morphisms | Second and third equations after `σ`, using `.map a.op` and `e.inverse.map a` | Naturality in both test objects and module pairs. |
| All semilinear transitions | Fourth equation after `σ`, using `transition` on both components | Product transition on the simultaneous site; fixed-level dispatcher uses identities. |
| s_!G = (G,0) | `IsIso (openAdj ... s).unit` and `∀ G, IsZero ((pull ... C.ι).obj ((extension ... s).obj G))` | Canonical first-component unit and zero complementary component. |
| Canonical projector π_s = (1,0) | `∃ π : 𝟭 ... ⟶ pull ... s ⋙ extension ... s` with s-restriction the unit and C-restriction zero | Natural system morphism pinned to the identity/zero projector. |
| Natural Hom bijection given by restriction and the identity open unit | `∃ H : ∀ F G, (...) ≃ (...)`; `IsIso` of b- and k-open units; `H F G a ≫ unit = restrictionSource ... F ≫ (pull ... k).map a` | Both Hom sets and the actual forward map are fixed; `restrictionSource` inserts the b-unit, inverse compositor, and s b = k. |
| Naturality in arbitrary F,G | Equation for `H F' G' ((extension ... b).map a ≫ f ≫ (extension ... k).map b)` | Contravariance in F and covariance in G both present. |
| Two maps equal when their restrictions agree | Separate `∀ F G (a b : ...), (pull ... k).map a = (pull ... k).map b → a = b` | Explicit restriction uniqueness in the actual abelian categories. |
| Ordinary open-unit comparison and substitution F=q*M | `∃ β : extension ... i ⋙ pull ... p ≅ pull ... q ⋙ extension ... b`; equation for `β.inv.app M` | Inverse is pinned as b-adjunct of q*η_i followed by `cartesianPull`; arbitrary F in H includes q*M. |
| No faithfulness of derived evaluation assumed | All Hom binders are morphisms in `Modules`; `sections` and `transition` are underived | No added hypothesis on derived evaluation. |

Repair findings and changes:

* H2: the plain abbreviation `Scheme.ProEt.clopenTestPiece` is owned by the
  landed existing definition node `def-pur-clopen-test-piece-inclusion`. Replaced
  `lem-pur-clopen-ringed-module-gluing` in the added `stmt_deps` with that node.
  Kept the gluing theorem in `proof_deps`, and corrected `lean.note` and the worker
  report sentence. The defining body is `MorphismProperty.Over.pullback`; it does
  not choose any data from the gluing theorem. The six other added statement
  dependencies are the landed definition nodes used by the dispatchers.
* H11: replaced the former paragraph with this explicit hypothesis-and-clause
  table. The second reading found no mathematical mismatch requiring a Lean
  change. It rechecked the empty U/W/C, Cartesian square, A₁, zero-module and
  arbitrary-transition cases and the small-site object/Hom universes described
  above. All helper data remain actual constructions and the sole postponed
  theorem is still the named item with its complete proof docstring.

No new node, dependency module, or statement correction is part of this repair.

Repair validation (2026-10-23 UTC): `scompile.py Q55 lem-sf-ambient-clopen-restriction-uniqueness` compiled the sandbox module and the named library module successfully, exit 0, without diagnostics. The JSON self-check confirmed the verbatim theorem signature and exactly seven added landed definition dependencies; every field other than `lean` and `stmt_deps` agrees with current main.
