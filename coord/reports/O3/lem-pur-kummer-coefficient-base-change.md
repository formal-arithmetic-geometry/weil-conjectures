## Worker report

The module `Sheaf.AlgebraicGeometry.KummerCoefficientBaseChange` states
`AlgebraicGeometry.Scheme.kummer_coefficient_base_change`, with one postponed proof (`sorry`).
It also supplies the standard finite-biproduct instance for abelian sheaves and the explicit
proposition `KummerIntegralLiftBoundary`, which is the integral-lift clause of this same node.
Neither definition contains postponed data or a proof obligation. No new DAG nodes or dependency
repair modules are needed. The existing, published `def-pur-kummer-module-coefficients` is added
to `stmt_deps` and its exact server source was checked with `scompile.py --source`.

The statement is unchanged. Its hypotheses and clauses correspond as follows.

- The fixed finite-field and coefficient datum is
  `P : WeilConjectures.PurityFiniteSetting.{u}`. This is the recorded
  `def-pur-conventions` construction, containing the finite field datum, its chosen algebraic
  closure `P.field.k`, the prime `P.coefficients.l` different from the characteristic, and the
  finite coefficient extension. Algebraic closedness of `P.field.k` comes from its existing
  `IsAlgClosure` instance; no separate arbitrary field replaces this datum.
- The independent exponent is `(N : ℕ) (hN : 1 ≤ N)`. The ring everywhere is the standard size
  lift `ULift.{u+1} (ZMod (P.coefficients.l ^ N))`, canonically the same residue ring R as in
  the text. It is not restricted to the special exponent `P.kummerLevel`.
- The coefficient object is `A : ModuleCat.{u+1} R`, with `Module.Free R A` and
  `Module.Finite R A`. These mean free of finite rank; since R is finite, A is finite as
  well. The statement does not assume A is a ring and does not restrict its rank to one.
  The parenthetical example A=A_(E,n), supplied by `lem-pur-finite-kummer-level`, is an
  example of this quantified coefficient module, not an extra conclusion or a hypothesis
  that e divides n for every A. That node presently has no `lean` or Mathlib record. Its
  statement was read; none of its twist-comparison or DVR facts is needed to *state* the
  present theorem, so no unrelated dependency theorem is invented or assumed here.
- `(C : Scheme.{u}) (f : C ⟶ Spec (CommRingCat.of P.field.k)) [IsCurve f] [Smooth f]`
  says exactly smooth separated curve over that k. The recorded `IsCurve` includes finite
  type, separatedness and dimension at most one. Connectedness, nonemptiness, properness
  and affineness are not assumed.
- `q : ℕ` renders every integer q≥0. Cohomology is `CategoryTheory.Sheaf.H`, the existing
  abelian-sheaf cohomology model used by the upstream Kummer boundary and this project's
  published Kummer-module interface. As explicitly permitted in the recorded
  `def-weil-pbc-etale-cohomology` note, its identification with `Etale.cohomology` on a sheaf
  in degree zero is the existing stage-3 bridge, not another cohomology definition here.
- F=mu_m is exactly `C.rootsOfUnitySheaf (P.coefficients.l ^ N)`, the kernel in the recorded
  Kummer sequence. The target abelian sheaf is
  `(kummerAbelianTwist C (P.coefficients.l ^ N)).obj A`. Its published implementation
  sheafifies U↦mu_m(U) tensor_R A and forgets scalar structure. Thus the constant sheaf A,
  sheaf tensor and underlying abelian cohomology are the ones specified by the node.
- `beta : ∀ q, (Sheaf.H F q ⊗[R] A) ≃ₗ[R] Sheaf.H (F tensor A) q` asserts an
  isomorphism in every degree. The first conjunct says
  `beta q (x ⊗ₜ a) = Sheaf.H.map (kummerCoefficientInsertion C m A a) q x`.
  This is precisely beta(x tensor a)=H^q(i_a)(x), including the required canonical map;
  it does not merely assert a bare nonempty isomorphism. Pure tensors determine beta.
- `hm : IsUnit (m : Γ(C, ⊤))` is supplied in the conclusion, not added as a hypothesis.
  It makes the *ordinary* boundary precisely
  `Sheaf.H.δSucc (C.kummerSequence_shortExact m hm) q`. Invertibility follows from the
  prime-to-characteristic datum. There is no R-module structure imposed on G_m.
- The existential additive family
  `delta : ∀ q, (Sheaf.H C.gmSheaf q ⊗[ℤ] A) →+ Sheaf.H (F tensor A) (q+1)`
  is the descended boundary of the node. Its pure-tensor equation is exactly
  `delta q (x ⊗ₜ[ℤ] a) = beta (q+1) (partial(x) ⊗ₜ a)`.
- `∀ q, KummerIntegralLiftBoundary C m q A (delta q)` retains the entire integral-lift
  specification, not just the final equation. The proposition quantifies over every
  abelian lift `L : ModuleCat.{u+1} ℤ`, every finite basis
  `b : Module.Basis (Fin r) ℤ L`, and every specified identification
  `e : (L ⧸ LinearMap.range ((m : ℤ) • LinearMap.id)) ≃ₗ[ℤ] A`.
  The quotient is literally L/mL: that range consists of m times elements of L.
  Every finite free integral lift has such a finite basis, so this basis formulation
  covers all lifts. The identification is additive/integral-linear, as in the text;
  R-linearity of any such identification follows from the unique residue-ring action.
- In that finite basis the sequence tensored with L is the short complex whose two
  arrows are `biproduct.map (fun _ : Fin r ↦ (C.kummerSequence m).f)` and its analogous
  `.g` map. This is exactly the finite direct sum of the ordinary sequence specified
  in the node. Existence of the zero-composite witness and its `ShortExact` proof are
  *conclusions*, not extra assumptions. No arbitrary exact sequence replaces it.
- The comparison `alpha` is an additive equivalence from H^q(G_m) tensor_Z L to
  H^q of the finite sum of G_m's. Its normalization is
  `alpha (x tensor l) = H^q(sum_j (b.repr l j) • biproduct.ι_j)(x)`.
  The map inside H^q is exactly g↦g tensor l in basis coordinates. Thus alpha is the
  natural cohomology-tensor identification in the node, not a free choice of automorphism.
- The left-term isomorphism `theta : (⨁ j, F) ≅ F tensor_R A` satisfies
  `biproduct.ι_j ≫ theta.hom = kummerCoefficientInsertion C m A (e [b_j])`.
  Since the inclusions determine a map from the finite biproduct, this fixes theta to
  the node's z tensor l↦z tensor e([l]) identification.
- The last equation of `KummerIntegralLiftBoundary` is
  `delta (x tensor e([l])) = H^(q+1)(theta)(δSucc hS q (alpha (x tensor l)))`.
  It says precisely that the boundary of the *actual* lifted sequence, after the two
  normalized comparisons, descends along L→L/mL=A to delta. Because this holds for every
  L, every e and every finite basis, and because the preceding pure-tensor equation
  determines delta uniquely, it includes independence of the lift and of its basis.
- At q=0 the ordinary δSucc is the global-sections Kummer connecting map under the
  existing `Sheaf.H.equiv₀` (`Sheaf.H.δSucc_zero` and upstream `kummerδ₀`). Thus the units
  class in degree one is included, rather than replaced by an unspecified class.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, its `field`
  and `coefficients`, together with `Sheaf.Paper.FiniteFieldFiber`'s `FiniteFieldDatum`.
- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve` (full class signature
  and docstring read; smoothness is `Smooth f`, not part of this class).
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`: `Scheme.rootsOfUnitySheaf`,
  `Scheme.kummerSequence`, and `Scheme.kummerSequence_shortExact`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `Etale.cohomology` and
  `Etale.rightDerivedGlobalSections` read; the recorded note permits the existing
  `Sheaf.H` abelian model used here, as in the published Kummer-affine-line theorem.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`:
  `SheafOfModules.siteSheafTensorRight` (read and imported for the proof plan).
- `Mathlib.Algebra.Homology.Additive`: `Functor.mapHomologicalComplex`, the recorded
  `def-kun-constant-sheaf` interface, read together with the record's specialization by
  `constantSheaf`. No new constant sheaf or constant complex is defined.
- Newly cited published node `def-pur-kummer-module-coefficients`, module
  `Sheaf.AlgebraicGeometry.KummerModuleCoefficients`: `Scheme.kummerAbelianTwist`,
  `Scheme.kummerCoefficientInsertion`, `kummerRootCohomologyModule` and
  `kummerModuleCohomologyModule`. All full definitions/docstrings were read; server source
  agrees with the shared copy. Its standard residue-ring actions are reused.
- Existing `CategoryTheory.Sheaf.H`, `.H.map` (Mathlib's SheafCohomology.Basic) and
  `.H.δSucc` (upstream `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`).
  The latter composes with the extension class of the specified short exact sequence.
- Proof imports: `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor` (full theorem and proof
  docstring read), `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
  (`CochainComplex.isKInjective_of_injective`, full signature read), and the tensor
  module above. Kummer exactness and constant-sheaf APIs are already public imports
  through the Kummer-module interface.

Edge cases checked before and after writing:

- A=0/rank zero is permitted by `Module.Free`/`Module.Finite`. No nonzero basis element
  or `Nonempty (Fin r)` is used. The lifted complex and comparison use empty biproducts.
- An empty curve is allowed: `IsCurve` requires dimension at most one, and there is no
  connectedness or nonemptiness assumption. The sheaf/cohomology and lift formulas
  remain meaningful; global sections of the empty scheme give the harmless zero ring.
- Disconnected curves and zero-dimensional components are allowed, matching `IsCurve`.
- q=0 and every higher natural degree occur in beta and delta. No positive-degree-only
  version of the coefficient comparison or boundary is substituted.
- N=1 is included; N=0 is excluded exactly by hN. The prime ell is different from the
  characteristic in P; no characteristic-zero or primitive-root hypothesis is added.
- A need not be a coefficient ring; integral L need not carry an R-module structure;
  G_m is used only as an abelian sheaf and tensored over Z.

Searches for an existing statement (2026-10-16):

- `msearch.py ... leanfinder "Etale cohomology commutes with finite free constant coefficient
  tensor and Kummer boundary"`: eight hits, all Kahler-differential/cotangent comparison
  results, including `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` and
  `Algebra.Generators.H1Cotangent.δ_eq`; no matching Kummer coefficient theorem.
- `msearch.py ... loogle "CategoryTheory.Sheaf.H, TensorProduct"`: zero hits.
- `msearch.py ... grep "kummer|Kummer|cohomology.*tensor" CategoryTheory/Sites`: zero hits.
- `msearch.py ... leansearch "Cohomology commutes with tensoring by a finite free constant
  module"`: service unavailable, Internal Server Error; no absence conclusion from this.
- `rg` for Kummer/coefficient comparisons in upstream `WeilConjectures`: existing Kummer
  sequence and affine-line computations, no theorem for arbitrary smooth separated curves
  with the integral-lift boundary clause. The exact node id has no upstream occurrence.
- `rg` in `lean/Sheaf` for Kummer and coefficient comparisons: found and reused
  `KummerModuleCoefficients` and its DAG node. `KummerAffineLine` has the comparison only
  for two specific curves and does not include the universal integral-lift boundary
  clause; it is not the present theorem. `PurityRelativeKummer` concerns relative direct
  images and also does not state this theorem. No duplicate statement was written.

Source verification: the blueprint Markdown is absent locally. The imported node text and
full `dag/units/sk-prop-a1-kummer.json` (especially its Coefficients step) were read. Official
Stacks pages were opened: [03PL](https://stacks.math.columbia.edu/tag/03PL) for the ordinary
short exact sequence, [015B](https://stacks.math.columbia.edu/tag/015B) for right-derived
cohomology and its delta-functor, and [03EK](https://stacks.math.columbia.edu/tag/03EK) for
sheafification of sectionwise tensors. The integral-lift formulation follows the node's
already corrected statement and five-step proof verbatim in mathematical content.

Validation: `scompile.py N3 lem-pur-kummer-coefficient-base-change
lean/Sheaf/AlgebraicGeometry/KummerCoefficientBaseChange.lean` succeeded without warnings
in both wrapper sandbox mode (14.2 s) and library-module mode (14.9 s). The initial compile
failed on a missing finite-biproduct instance and on notation for mL; both were repaired
using the standard instance and `LinearMap.range` respectively. All lines are ≤100 columns.
The signature is recorded verbatim in the sandbox node. Dry-run results are recorded below.
No statement dispute or source-based statement correction was needed.

Required delivery dry run completed successfully:
`OK (dry run): commit 09515162bc compiles and passes the preflight except for the second
reading, which the second reader writes; nothing pushed.` The second-reading section is
intentionally left for the independent reader, as instructed by the delivery tool.


## Second reading by N3

I independently read the node, original blueprint (retrieved read-only into
scratchpad/source-blueprint.md), unit sk-prop-a1-kummer and the submitted Lean file. The original
blueprint's final displayed sequence tries to tensor G_m with A over R, although G_m is not an
R-module. The node was already corrected in stage 1: it tensors the ordinary sequence with a free
integral lift and descends its boundary. This delivery preserves that baseline statement; there is
no new statement_change.

I read Stacks etale-cohomology.tex, section-kummer and lemma-kummer-sequence (Tags 03PK/03PL);
derived.tex, lemma-higher-derived-functors and lemma-right-derived-delta-functor (015B/05TE); and
sites-modules.tex, section-tensor-product and lemma-sheafification-tensor (03EK). The TeX copies
were retrieved read-only into the sandbox scratchpad. Kummer requires a positive integer invertible
on the scheme; it requires no Noetherian, properness, or connectedness assumption. The derived
statement requires abelian categories, enough injectives and left exact sections, supplied by the
small-site sheaf framework. The tensor construction is sheafification of sectionwise tensor, and
tensor commutes with sheafification. These hypotheses agree with the node and Lean below.

Objects, hypotheses and conclusion clauses, matched independently:

- Fixed datum: `P : WeilConjectures.PurityFiniteSetting.{u}` supplies the finite-field datum, its
  algebraic closure `P.field.k`, and prime `P.coefficients.l` different from the characteristic. I
  read `PurityFiniteSetting`, `FiniteFieldDatum`, and `CoefficientDatum`. Verdict: the fixed field
  and prime of the conventions, with no replacement datum.
- Positive exponent and residue ring: `(N : ℕ) (hN : 1 ≤ N)` and `ULift.{u+1} (ZMod
  (P.coefficients.l ^ N))` render N >= 1 and R = Z/ell^N. Verdict: all positive exponents,
  independent of the datum's special `kummerLevel`; the ULift is only the established size
  convention.
- Coefficient module: `A : ModuleCat.{u+1} R` with `Module.Free R A` and `Module.Finite R A`.
  Verdict: exactly finite rank freeness; R is finite, so A is finite. Rank zero is permitted, and A
  is not required to be a ring. The A_(E,n) parenthesis is an example, not another quantified
  conclusion. I read the example node `lem-pur-finite-kummer-level`; none of its twist/DVR objects
  is needed in this signature, so its unstated theorem creates no missing object here.
- Curve: `(C : Scheme.{u}) (f : C ⟶ Spec (CommRingCat.of P.field.k)) [IsCurve f] [Smooth f]`. The
  opened `IsCurve` class extends separatedness, locally finite type and quasi-compactness, and
  bounds dimension by one. Verdict: exactly a smooth separated curve, including the empty,
  disconnected and zero-dimensional cases in `def-sc-curves`.
- Site and cohomology: the reused roots and twist lie in `Sheaf C.smallEtaleTopology
  AddCommGrpCat.{u+1}` and `Sheaf.H` is their abelian cohomology. I read the recorded Etale
  derived-cohomology interface and its note permitting the existing Sheaf.H spelling with a stage-3
  bridge. Verdict: same small etale site and underlying abelian-sheaf cohomology; no alternative
  cohomology definition.
- Roots and tensor sheaf: `C.rootsOfUnitySheaf m` is the kernel of `m • 𝟙 C.gmSheaf`;
  `(kummerAbelianTwist C m).obj A` sheafifies the sectionwise root tensor with the constant module.
  I followed the published definitions through `finiteEtaleMuModulePresheaf`, scalar restriction by
  `ULift.ringEquiv`, and `kummerModuleTwist`. Verdict: precisely F and F tensor_R A. Stacks 03EK's
  sheafification-tensor identity justifies using the constant presheaf before sheafification.
- All degrees: `beta : ∀ q : ℕ, ... ≃ₗ[R] ...` is the comparison isomorphism in every q >= 0. Its
  equation `beta q (x ⊗ₜ a) = Sheaf.H.map (kummerCoefficientInsertion C m A a) q x` fixes the
  canonical map on pure tensors. Verdict: every comparison and its stated characterization, rather
  than an arbitrary isomorphism. The coefficients' residue-ring actions are the published
  `kummerRootCohomologyModule` and `kummerModuleCohomologyModule`.
- Ordinary boundary: `hm : IsUnit (m : Γ(C, ⊤))` is a conclusion, and `Sheaf.H.δSucc
  (C.kummerSequence_shortExact m hm) q` uses the actual ordinary sequence. Verdict: invertibility
  follows from the fixed characteristic and prime, without an extra hypothesis; the boundary is
  precisely partial^q.
- Descended boundary: `delta : ∀ q : ℕ, (Sheaf.H C.gmSheaf q ⊗[ℤ] A) →+ Sheaf.H ((kummerAbelianTwist
  C m).obj A) (q+1)` and its pure-tensor equation render partial_A^q(u tensor a) =
  beta_A^(q+1)(partial^q(u) tensor a). Verdict: exact source, target, degree and formula. G_m has no
  imposed R-action.
- Universal integral lift: `KummerIntegralLiftBoundary` quantifies over every `L : ModuleCat.{u+1}
  ℤ`, rank `r`, finite basis `b : Module.Basis (Fin r) ℤ L`, and specified `e : (L ⧸ LinearMap.range
  ((m : ℤ) • LinearMap.id)) ≃ₗ[ℤ] A`. The range is exactly mL. Every finite free integral group
  admits such a finite basis. Verdict: every lift and identification in the node, with basis
  coordinates expressing its finite direct sum.
- Lifted sequence: the two arrows are `biproduct.map` of the ordinary Kummer `.f` and `.g`. `w`
  proves their composite zero and `hS` asserts short exactness, both existential conclusions.
  Verdict: the actual finite direct sum of the ordinary sequence, with no arbitrary replacement
  arrows or exactness assumption.
- Cohomology identification for the last term: `alpha` is an additive equivalence from H^q(G_m)
  tensor_Z L to the cohomology of the finite sum. Its equation uses `Sheaf.H.map (∑ j, (b.repr l j)
  • biproduct.ι ... j) q x`. Verdict: precisely the natural map induced by g maps to g tensor l,
  fixed on all pure tensors.
- Left-term identification: `theta` identifies the finite sum of F with F tensor_R A and is
  normalized by `biproduct.ι ... j ≫ theta.hom = kummerCoefficientInsertion ... (e [b j])`. Verdict:
  exactly z tensor l maps to z tensor e([l]); the biproduct injections determine the entire map.
- Descent of the lifted boundary: the final equality compares `delta (x ⊗ₜ[ℤ] e [l])` with
  `Sheaf.H.map theta.hom (q+1) (Sheaf.H.δSucc hS q (alpha (x ⊗ₜ[ℤ] l)))`. Verdict: the actual lifted
  connecting map descends to the same delta for every L, e and b. Together with the pure-tensor
  formula this gives independence of all choices, since pure tensors generate the domain.
- Units class: q = 0 is included, and the opened upstream `Sheaf.H.δSucc_zero` identifies this
  boundary with the global-sections boundary used in `kummerδ₀`. Verdict: the usual units Kummer
  class is retained.

Edge cases: A = 0 and rank zero use empty `Fin 0` biproducts, with no nonempty-index assumption.
Empty curves give the zero sheaf groups and the harmless zero section ring, in which the stated unit
conclusion holds. Disconnected curves and zero-dimensional components remain included by IsCurve. N
= 1 is included, N = 0 is excluded exactly as the source requires, and ell is prime to the fixed
characteristic. Degrees include zero and all higher naturals. Scheme universe u and standard module
universe u+1 match the recorded small etale APIs. Finite coefficient modules and finite free
integral lifts of any size have equivalent representatives in these universes, so this convention
excludes no mathematical coefficient or lift.

Independent duplicate searches (2026-10-16), using different queries from the first worker:

- LeanFinder: "An additive cohomology functor commutes with extension by a finite free constant
  module and connecting morphisms" returned eight group-cohomology/Ext and connecting-map facts,
  including `groupCohomologyIsoExt` and `groupCohomology.δ_apply`; none states this Kummer
  coefficient comparison and integral-lift clause.
- Loogle: `"H", "tensor"` returned twelve generic tensor-product constructors and maps, including
  `TensorProduct.liftAddHom`; no sheaf Kummer comparison.
- LeanSearch: "Kummer sequence cohomology tensor finite free coefficients natural boundary" was
  unavailable (Internal Server Error). No absence claim rests on that service.
- msearch grep: `H.*(tensor|Tensor)|[Tt]ensor.*(cohomology|Cohomology)|[Kk]ummer` in
  `CategoryTheory/Sites` returned six monoidal/stalk tensor hits, none the statement. Independent rg
  searches over Mathlib, upstream WeilConjectures and project Sheaf found the ordinary
  Kummer/connecting APIs, the reused KummerModuleCoefficients module, the two-curve KummerAffineLine
  special case and unrelated quasi-coherent tensor comparisons; no exact existing full statement.
  Full-name searches also found no pre-existing `KummerIntegralLiftBoundary` or main theorem.

I checked the stage-1 correction audit against two original citers: `prop-pur-gm-relative-kummer`
step 5 uses exactly the retained coefficient isomorphism and boundary, so its holds:true verdict is
valid. `prop-pur-affine-line-orientation-base-change` historically asked this coefficient theorem to
supply geometric pullback naturality, which neither version did, explaining the recorded
holds:false. Its current proof obtains pullback naturality elsewhere and no longer lists this item
as a direct dependency. The current direct-citer scan has only the relative-Kummer node;
`thm-pur-kummer-affine-line` is not a direct dependency citer either. No new statement correction or
citer edit was made.

H4/H5/H6/H8/H9 checks: the only new Prop is the integral-lift clause belonging to this node, not a
second tensor/cohomology construction; the finite-biproduct instance uses Mathlib's standard
construction. Definitions contain real data and the only theorem is postponed with sorry. Each
declaration has the source/blueprint docstring, and the theorem docstring follows all five node
proof steps. No new definition node or dependency module occurs in this packet. The exact server
KummerModuleCoefficients source agrees with the shared copy apart from a trailing blank line. The
recorded theorem signature equals the file verbatim, all variables/universes are explicitly bound,
and the maximum Lean line width is 95.

No mathematical or Lean mismatch was found. I changed only this report by adding the independent
reading, source/citer audit and repeated searches. Independent `scompile.py` verification succeeded
cleanly for the sandbox and library module (14.9 s and 16.8 s), with the required wrapper and no
global build. Final dry-run and delivery results follow.

Final dry run: `OK (dry run): commit 1822035856 passes the preflight and compiles; nothing pushed`.
