## Worker report

The module `Sheaf.Paper.FiniteKernelConstructibleLocalization` states
`WeilConjectures.finiteKernelConstructibleLocalization`, with `sorry`. It reuses the actual
support-kernel functor, the ordinary constant-ring module adjunctions, and their canonical
K-injective or exact termwise derived functors. No theorem is proved in this delivery.
The three helpers are a positive-level coefficient abbreviation, its existing finiteness
instance, and the canonical scalar operation on derived morphisms through the existing
constant-section realization. The remaining instance supplies left exactness of a right
adjoint from its existing adjunction. All have real data.

Hypothesis and clause correspondence:

- A field k is `(k : Type u) [Field k]`. A prime l is `(l : ℕ) [Fact l.Prime]`.
  Its invertibility in k is `_hl : IsUnit (l : k)`.
- The finite extension is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The recorded coefficient ring contains the valuation
  ring and its recorded chosen uniformizer. `sfKernelCoefficient l E n` abbreviates exactly
  `Padic.coefficientExtensionRing l E (n+1)`. Every positive exponent occurs, including one;
  no exponent-zero case from the statement is lost because the node requires n≥1.
- The separated finite-type k-scheme is `t : X ⟶ Spec (.of k)` with
  `[LocallyOfFiniteType t] [QuasiCompact t] [IsSeparated t]`. No finite-field datum, algebraic
  closure of k, bound on its cohomological dimension, or Tor hypothesis is present.
- `i : Z ⟶ X [IsClosedImmersion i]`, `j : U ⟶ X [IsOpenImmersion j]`, and
  `_hij : Set.range j = (Set.range i)ᶜ` give the complementary closed/open pair. The maps
  to Spec k on U and Z are j≫t and i≫t, so no independent structure or compatibility
  hypothesis is required. Quasi-compactness of j is a consequence of this setting.
- The ambient categories are `proEtaleDerivedCategory T (sfKernelCoefficient l E n)`.
  These are the published uncompleted small-pro-etale constant-ring module derived
  categories: site objects in u+1, morphisms in u, coefficient modules in u+1, and the
  standard derived localization. The finite subcategories are selected by
  `intrinsicFiniteTorsionConstructible l E (n+1) (Nat.succ_pos n) T`. The imported integral
  category is `sfIntegralConstructibleCategory`; the item makes no integral-stage claim.
- `sfIntrinsicClosedUpperShriek i j A` is precisely the recorded underived i!_0: the
  functor `sfIntrinsicSectionsWithSupport j A` takes the kernel of the actual open module
  adjunction unit and then `sfConstantModulePullback i A` is applied. No copy is made.
- The conclusion first supplies right exactness `hcol` of closed direct image. The helper
  `sfKernelPush_limits` obtains left exactness from `sfConstantModuleAdjunction`. These
  instances type its exact termwise `mapDerivedCategory`; neither is an added assumption.
  The explicit instance lambda merely installs this proved-in-the-conclusion witness.
- The existential sheaf adjunction `a0 : sfConstantModuleDirectImage i A ⊣
  sfIntrinsicClosedUpperShriek i j A` is normalized by the equation, for every sheaf N,
  `closedUnit(supportKernel N) ≫ a0.counit.app N = kernel.ι(openUnit N)`; that closed unit
  is also asserted invertible. Thus the exceptional counit is the actual kernel inclusion,
  rather than an arbitrary adjunction counit.
- `a0.mapDerivedCategoryRightDerivedAdjunction` is the published ambient adjunction
  `D(i_*) ⊣ R(i!_0)`, constructed by the standard K-injective total right derived functor.
  It exists on all unbounded objects; no boundedness of its output is needed to type it.
  The expression `.rightDerivedFunctor` is that actual total derived functor, computed on
  every K-injective representative by the published `rightDerivedFunctorObjQIso`.
- Coefficient linearity is the displayed equality `R(i!_0).map (sfKernelScalar X A a f) =
  sfKernelScalar Z A a (R(i!_0).map f)`, together with `Functor.Additive`.
  `sfKernelScalar` conjugates the usual `ULift A` scalar action through the canonical
  derived realization equivalence. Its counit maps account for its objects. Thus it is
  the usual constant-section A-action on all derived morphisms, not an unconstrained
  existential module action. `Functor.IsTriangulated` gives exactness with the canonical
  derived shift structure. All three properties are ambient, and hence restrict.
- Four preservation clauses assert that Ri!_0, i*, j*, and i_* preserve the indicated
  intrinsic predicates. A fifth preservation clause is precisely Rj_* preserving D^b_c.
  On the full subcategories, the canonical ambient Hom bijections therefore restrict
  verbatim to an adjunction. Fullness means the same unit and counit are used. It is not
  necessary to choose new restricted functors or new Hom bijections to state this.
- The `∀ M : proEtaleDerivedCategory X A` clause supplies the ordinary triangle for every
  unbounded object. Its first and second maps are explicitly
  `exceptionalOpenAdjunction.counit` and `finiteRecollementDerivedAdjunction.unit`.
  It uses the `finiteDerivedPullback` of the recorded operations dependency, not a free
  inverse-image functor. `Triangle.mk ... δ ∈ distTriang ...` gives distinguishedness.
- For every intrinsically constructible K, the next clause asserts the supported
  distinguished triangle. Its first map is literally
  `a0.mapDerivedCategoryRightDerivedAdjunction.counit.app K`. Its second is literally
  the canonical open derived adjunction unit. The vertices are the prescribed
  `D(i_*) R(i!_0) K`, K, and `Rj_* j* K`. Their constructibility follows from the
  preservation clauses; distinguishedness is tested in the ambient derived category,
  which is the inherited triangulation of the full constructible category.
- For every P,G satisfying the intrinsic predicates and every `m : ℤ`, the Hom type
  `((D(i_*) P)⟦m⟧ ⟶ Rj_* G)` is `Subsingleton`. Since the categories are preadditive,
  this is exactly the assertion that this Hom group is zero.
- The final three clauses say that the ordinary closed counit is invertible on bounded
  constructible P, that this very natural transformation has `NatTrans.CommShift ... ℤ`,
  and that on `Q I` it is precisely the image of the termwise sheaf counit, preceded by
  the two canonical exact-functor factorization maps. This retains the signed shift
  comparison, with no arbitrary objectwise isomorphism replacing the counit.
- No occurrence of `finiteTorConstructible` or any finite-Tor subcategory is used.

Canonical-operation coordinates: `sfConstantModulePullback` and `sfConstantModuleDirectImage`
are the existing ordinary module operations along the canonical inverse-image constant-ring
isomorphism `sfConstantCoefficientIso`. The normalized `sfConstantModuleAdjunction` is the
published tensor-unit adjunction. The canonical finite operations also have the fixed-scalar
realization presentation used by the ordinary triangle. These are two published presentations
of the same actual operations; no new coefficient identification is selected in this delivery.
The ringed support-kernel dependency is imported and remains the ambient proof input for the
constant-coefficient specialization. Its full theorem and kernel/counit definitions were read.
The integral-constructible dependency is used only for its imported category convention and
intrinsic finite predicate: there is no finite-base restriction silently introduced.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, importing `coefficientExtensionRing`, its actual
  valuation-ring quotient construction, and the chosen uniformizer.
- `def-weil-scheme-morphism-properties` is explicitly a convention node with no declaration.
  Its Mathlib properties are `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`,
  `IsClosedImmersion`, and `IsOpenImmersion`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`; its imported finite predicate is the intrinsic one.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint`:
  `ringedSupportKernel`, `ringedClosedKernelShriek`, `ringedClosedKernelResolutionIso`,
  and `proEtale_ringed_closed_kernel_adjoint` (the full sheaf and unbounded derived theorem).
- Mathlib `Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`;
  its definition is null homotopy of every map from an acyclic complex, as the node requires.
- `Sheaf.Paper.SfDerivedDirectImage`: `sfFiniteDerivedDirectImage`, with finite level the
  recorded ordinary K-injective `proEtaleConstantDerivedDirectImage`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`; its intrinsic exact
  pullback is the recorded termwise descent. No integral or rational operation is used.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedSupport`:
  `sfIntrinsicClosedUpperShriek`, `sfIntrinsicSectionsWithSupport`, and
  `sfConstantModuleAdjunction` (already landed, used rather than copied).
- `Sheaf.AlgebraicGeometry.FiniteOpenClosedRecollement`:
  `finiteRecollementDerivedAdjunction`; and `IntrinsicDerivedOpenAdjunction`:
  `exceptionalOpenAdjunction` (already landed actual maps).
- `Sheaf.SixFunctors.OpenTensorNormalizationData`:
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`, whose data is the
  localization of the actual termwise adjunction, was read and is used unchanged.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicDerivedEquivalence`, the derived equivalence of the actual canonical
  coefficient realization, is used only to express scalar multiplication without a
  separately chosen scalar structure on intrinsic modules.

The item's stmt_deps gains the three already-landed definition nodes
`def-exc-proetale-sections-with-support`, `def-weil-open-closed-recollement`, and
`def-weil-exact-derived-adjunction`, which own the directly used canonical constructions.
No statement text, proof, or proof dependency is changed. No new node or dependency repair.
Every published proof-dependency module is imported; Mathlib leaves are available from
these imports, including exact-functor triangulation and the triangulated-adjoint theorem.

Edge cases checked before writing: X empty; Z empty (U=X); U empty (Z=X); zero complexes;
positive exponent one and exponent two; negative, zero, and positive shifts; arbitrary
non-closed and positive-characteristic fields with l invertible. Kernels and counits remain
actual in the empty cases; zero Hom groups are Subsingleton, never IsZero of a bare type.
The exponent-two case retains constructible nonperfect modules such as the residue module,
so replacing the category by finite-Tor objects has not occurred. The three scheme and
coefficient sizes fit simultaneously in u; there is no equation between the pro-etale site
object universe u+1 and its morphism universe u.

Searches for an existing complete statement:

- `msearch.py`, leanfinder: "Finite coefficient constructible pro etale derived closed
  support kernel localization triangle" — eight unrelated hits (etale locus, derived
  fractions, isGE); no constructible support-kernel localization statement.
- `msearch.py`, loogle: "Functor.rightDerivedFunctor, Adjunction.mapDerivedCategory,
  Triangle.mk" — no hits, unknown first identifier in this search index.
- `msearch.py`, grep: "ringedClosedKernelShriek|constructible.*localization" — no Mathlib hit.
- `msearch.py`, leansearch: "The derived closed support kernel functor preserves bounded
  constructible complexes on the pro etale site" — eight general pullback, ideal-kernel,
  and derived-t-structure hits; no requested statement.
- `rg` of project `Sheaf` and `WeilConjectures`: `ringedClosedKernelShriek`, the item id,
  `sfIntrinsicClosedUpperShriek`, and constructible finite operations. Found the ambient
  ringed theorem and intrinsic kernel/ambient-adjunction modules, which are reused; no
  complete matching theorem. Related `SfLocalizationAllStages` packages other assertions
  and lacks this kernel/counit/termwise-normalization interface, so is not an exact match.
- `rg` of Mathlib algebraic geometry and sites: "constructible.*localization" and
  "support.*kernel.*derived" — no requested statement.
- `rg` of project sources and `dag/lean_names_upstream.json`: the new names
  `sfKernelScalar`, `sfKernelCoefficient`, `finiteKernelConstructibleLocalization` — no clash.

Validation: the module compiled on the server in both sandbox and actual module name
with no errors or warnings. All declared variables and universes are explicit;
`set_option autoImplicit false` is enabled. The only postponed proof is the named item
with its complete ten-step DAG proof plan in the docstring. No STATEMENT-DISPUTED issue.

## Second reading by Q101

Self-review after the clean server compile; no independent reviewer was started, in
accordance with the dispatcher brief. The maintainer supplies the independent review.

Read the item statement again alongside the complete Lean signature. Checked every
field, prime, coefficient extension and positive-level condition; the explicit structure
map t imposes exactly separated finite type. Read the underlying canonical kernel module
and confirmed the adjunction unit used to take its kernel. The exceptional sheaf counit
is tied to this inclusion by the closed unit equation; its derived counit is exactly the
canonical unbounded K-injective derived adjunction. Checked the ordinary triangle uses
the recorded finite operations and actual maps, and the supported triangle uses its
actual exceptional counit and open unit. Preservation for Ri!_0, i*, j*, i_* and Rj_*
uses only the intrinsic predicate. The ambient adjunction and full-subcategory
preservation imply the restricted exact right adjunction without any Tor restriction.
Checked m ranges over all integers and the vanishing is the zero Hom group. Finally
read the localized counit formula against the published exact termwise adjunction:
the two factors and Q of the termwise counit have the correct source and target;
`NatTrans.CommShift` refers to this exact natural transformation and its actual shifts.

Corrections made during this reading: replaced an existential open adjunction in the
ordinary triangle with the published `exceptionalOpenAdjunction`, so its first arrow
is normalized; retained both the termwise closed counit formula and its shift square;
added explicit pullback preservation to make restriction to full subcategories visible;
wrapped all lines to at most 100 characters. No mathematical statement correction.
