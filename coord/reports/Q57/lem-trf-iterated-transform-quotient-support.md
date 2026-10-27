## Worker report

The module `Sheaf.AlgebraicGeometry.IteratedTransformQuotientSupport` states the
node in two theorems, both with `sorry`. It adds no definitions, no new nodes,
no dependency repairs and no statement correction. The source read was Stacks
`divisors.tex`, definition-strict-transform (080D), its preceding paragraph,
and lemma-strict-transform-composition-blowups (080I), including its whole proof.
The latter's first paragraph and the first three sentences of the next paragraph
are precisely the two-quotient and support calculation extracted in this node.

Hypothesis and clause correspondence:

- The schemes S and X and morphism f are `{X S : Scheme.{u}} (f : X ⟶ S)`.
  The universe u is arbitrary, with no dimension, finiteness, separatedness or
  Noetherian hypothesis on these schemes or on f.
- The first centre is `(I : S.IdealSheafData) [I.toModules.IsFiniteType]`.
  `IdealSheafData` represents a quasi-coherent ideal; its `toModules` is the
  actual ideal sheaf. The second centre is
  `(J : I.blowup.IdealSheafData) [J.toModules.IsFiniteType]`.
  Thus S1, S2, b0, b1 are I.blowup, J.blowup, I.blowupMap, J.blowupMap.
- A is `Limits.pullback f I.blowupMap`, p is its `pullback.fst`, and f1 its
  `pullback.snd`. B is the iterated fibre product
  `Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap`, q its first
  projection and f2 its second. This is the displayed identification of B
  with A ×[S1] S2, canonically also X ×[S] S2.
- The quasi-coherent input is `(F : X.Modules) [F.IsQuasicoherent]`.
  M is `moduleStrictTransform f I F`, using the recorded definition.
  The conclusion `∃ h₁ : M.IsQuasicoherent` asserts its quasi-coherence and
  supplies the proof required to type N. It is not a new hypothesis.
- N is `@moduleStrictTransform _ _ (pullback.snd f I.blowupMap) J
  inferInstance M h₁`; its `.IsQuasicoherent` is the next conjunct.
- The existentially bound α has source q*p*F and target exactly N. Its first
  conjunct fixes it by equality to `(tensorPullback q).map pi0 ≫ pi1` with
  the two recorded `moduleStrictTransformπ` maps. Thus no arbitrary quotient
  is substituted for the canonical composite. `Epi α` is sheaf surjectivity;
  it does not assert surjectivity on sections over every open.
- The open in the `IsIso ((restrictFunctor ...).map α)` clause is
  `((q ≫ p ≫ f) ⁻¹ᵁ I.support.compl) ⊓
   ((q ≫ f1) ⁻¹ᵁ J.support.compl)`.
  The fibre-product equalities identify q p f with f2 b1 b0 and q f1 with
  f2 b1, so this is exactly B minus (T_I union T_J), including its open scheme.
- The final quantified clause takes every open W and every section s of
  q*p*F killed by α, and says its image under the restriction adjunction unit
  to this same open is zero. This is precisely s restricted to W intersect
  that complement. Sections killed by α are the sections of ker α, via the
  canonical kernel inclusion, so this renders the whole local-section clause.
- `iteratedModuleStrictTransform_quotient_structureSheaf` specializes to
  `SheafOfModules.unit X.ringCatSheaf` and explicitly uses its recorded
  quasi-coherence proof. It asserts quasi-coherence of the first transform,
  and `Epi` for the composite from O_B obtained using epsilon_q inverse,
  q* of `moduleStrictTransformStructureMap f I`, and pi1. Its equation says
  that applying epsilon_q inverse and q* of epsilon_p inverse to alpha
  gives exactly this canonical quotient. Here epsilon_p and epsilon_q are
  the multiplication maps `tensorPullbackObjUnitToUnit`; their inverses use
  the `.1` isomorphism proof of `tensorPullbackObjUnitToUnit_isIso`.
  This equation and Epi give the final structure-sheaf clause with its
  required normalization, rather than merely an unspecified quotient.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly supplies the existing
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType` interfaces
  recorded by pqf-def-coherent. No second quasi-coherence definition is made.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and
  `blowupMap`; `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`
  gives `toModules` as the kernel of the closed-subscheme quotient.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, with schemes' pullback instance.
- `Sheaf.AlgebraicGeometry.ModuleStrictTransform`: `moduleStrictTransform`
  and the kernel/restriction definitions behind it.
- `Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel`:
  `moduleStrictTransformπ`, `moduleStrictTransformStructureMap`, and the
  proof input `moduleStrictTransform_properties`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` exposes the
  actual upstream `tensorPullback`, with its normalized adjunction and
  `tensorPullbackSectionComp` needed for the restriction/pullback argument.
- `Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction`:
  `restrictFunctorIsoTensorPullback` and its unit theorem are proof inputs.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  `tensorPullbackObjUnitToUnit`, `tensorPullbackObjUnitToUnit_isIso`.
- The Mathlib leaf lem-weil-pbc-module-pullback-epi-direct-sum records
  `Functor.preservesEpimorphisms_of_isLeftAdjoint`, together with
  `PreservesCoproduct.iso` and `ι_comp_sigmaComparison` for its unused second
  clause. Read the signatures; only the epimorphism clause is needed here.
  Transport along the unique left-adjoint comparison applies it to the
  actual tensor pullback, without assuming preservation as an extra premise.

The module imports the stated proof dependencies; the ordinary restriction
functor and adjunction are those of Mathlib `AlgebraicGeometry.Modules.Sheaf`.
It deliberately does not import the downstream
`StrictTransformComparisonEpimorphism` module, whose real helpers spell out
this same second transform and quotient. The expressions here use those
underlying constructions directly, without duplicating any helper definition
or creating an import cycle when that consumer later imports this theorem.

Edge cases checked mathematically before writing:

- Empty X or S: the modules and restriction formulas remain well typed, and
  the support condition includes the empty open.
- I = 0, or J = 0: the corresponding blowup is empty; no nonempty hypothesis
  is imposed and the quotient/support conclusions remain valid.
- Unit centres: the complementary open is the whole base and the associated
  transform is unchanged. If both centres are units, α is an isomorphism
  globally and its kernel has no nonzero sections.
- F = 0: the two transforms and quotient are zero, with all clauses valid.
- Nontrivial torsion: on Spec(k[t]) with I=(t), J=(1), and
  F=O plus O/(t), the first quotient discards O/(t). That kernel is supported
  on V(t), while the restriction on D(t) is invertible. This rules out an
  accidental global-isomorphism assertion or global-section-surjectivity claim.
- No composite-blowup centre K, union condition V(K), or finite-type hypothesis
  on F is added: those belong to the downstream comparison, not this node.

Searches actually run with msearch.py, group Q57 and this item:

- leanfinder: "Two successive module strict transforms have a surjective
  composite quotient isomorphic away from the two blowup centers" returned
  eight unrelated adic completion, ramification and module-quotient hits;
  none states the scheme/module assertion.
- loogle: `AlgebraicGeometry.Scheme.Modules, "strictTransform"` returned 0 hits.
- grep in Mathlib/AlgebraicGeometry:
  `iterated.*[Tt]ransform|[Tt]ransform.*[Qq]uotient|strictTransform` returned 0 hits.
- leansearch: "The canonical quotient onto two successive module strict
  transforms is an isomorphism away from the inverse images of the two centers"
  returned eight submodule quotient, ModuleCat epi and ideal quotient hits;
  none states this sheaf assertion.
- rg over `lean/WeilConjectures` and `lean/Sheaf` for strictTransform,
  strict_transform, moduleStrictTransform and iterated/successive variants
  found the recorded single-transform definitions, separate admissible-blowup
  calculus and the downstream comparison helpers/theorem. The comparison
  imposes an additional K and identifies a different quotient; it does not
  state the present invertibility or kernel support off the two centres.
- rg for the item's id in `lean/WeilConjectures` returned no match. The exact
  new theorem names were checked against `dag/lean_names_upstream.json`.

No statement dispute or dependency fault found. Compile via scompile.py passed
both sandbox and library module modes (10.4 s and 11.3 s before the final
explicit proof-import addition). Final validation is the delivery dry run.

## Second reading by Q57

I re-read the node and final module clause by clause in this same worker session;
no independent worker was started, as the dispatcher brief prohibits doing so.
The maintainer performs the independent review of the delivery.

The check confirmed that finite type belongs to both centre ideals, not to F;
that h₁ is a conclusion rather than an added input; that α is constrained to
q*(pi0) followed by pi1; and that the complement used in both the isomorphism
and support clauses is the intersection of the two inverse-image complementary
opens. I checked its maps against the fibre-product identities to avoid
confusing V(J) on S1 with a subset on S. The support clause is conditional on
α(s)=0, so it asserts kernel support rather than that every source section
vanishes there. In the structure-sheaf theorem the two inverses are in the
correct order, and the normalized source is O_B. This reading found no
statement mismatch. I added the explicit structure-sheaf proof dependency
import; no node text or mathematical hypothesis changed.
