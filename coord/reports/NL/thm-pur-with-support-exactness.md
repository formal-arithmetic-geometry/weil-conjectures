## Worker report

The delivery states `AlgebraicGeometry.exists_support_longExact` in
`lean/Sheaf/AlgebraicGeometry/SupportLongExact.lean`. It has one postponed theorem,
with `sorry` as its entire proof. Its docstring follows all eight steps of the
DAG proof and names the corresponding proof dependencies. All other declarations
are concrete maps or notation-sized presentations of the assertion. No definition
chooses a boundary map, an injective resolution, or an unspecified canonical map
from a mere existence theorem. The theorem asserts existence of the boundary
family, as the node does.

Source checked: Milne, *Lectures on Etale Cohomology*, v2.21, Section 9,
Theorem 9.4, printed pp. 65–67, https://www.jmilne.org/math/CourseNotes/LEC.pdf.
The support kernel and displayed long exact sequence agree with the node. The
bounded-below, arbitrary-scheme and pro-etale clauses follow the explicit site
proof in the DAG, rather than adding Milne's general locally Noetherian convention.

Hypotheses and clauses are rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| A scheme X | `{X : Scheme.{u}}`, with no finiteness, field, or nonemptiness hypothesis. |
| Closed subscheme i : Z → X | `(i : Z ⟶ X) [IsClosedImmersion i]`. Nilpotent structures are allowed. |
| Its open complement j : U → X | The existing `Etale.supportRestrictionArrow i` and `ProEtale.supportRestrictionArrow i`, with open object `Scheme.Etale.mk i.openComplement.ι` or `Scheme.ProEt.mk i.openComplement.ι` and terminal object `mk (𝟙 X)`. This uses the actual open complement from the support dependency. |
| A torsion abelian etale sheaf F | Apply the etale factor to F in degree zero. `Etale.supportSequenceCoefficients X` is just `ObjectProperty.inverseImage Scheme.HasTorsionEtaleCohomology DerivedCategory.Plus.ι`. A torsion F placed in degree zero satisfies exactly this existing predicate: its only possible nonzero cohomology sheaf is F. It is the locally torsion predicate, not a uniform annihilator condition. |
| H^q_Z(X,K) | `Sheaf.supportHypercohomologyFunctor X.smallEtaleTopology AddCommGrpCat (Etale.supportRestrictionArrow i) q`. Its value is definitionally `Etale.supportHypercohomology i q K` from the recorded dependency. Similarly for pro-etale modules and `ProEtale.supportHypercohomology`. |
| H^q(X,K) | `Sheaf.sectionHypercohomologyFunctor ... (Scheme.Etale.mk (𝟙 X)) q`, namely cohomology of the bounded-below right derived functor of evaluation at the terminal object. This is global hypercohomology, not underived evaluation of the cohomology sheaf. |
| H^q(U,j⁻¹K) | The same derived evaluation at the open object. Localization and injective-preserving restriction identify this with the hypercohomology of the restricted coefficient on U. The relevant localization and comparison proof modules are imported. No acyclicity of the original sheaf is assumed. |
| The first arrow | `supportHypercohomologyInclusion`, obtained by `Functor.rightDerivedFunctorPlusNatTrans` from `supportedSectionsInclusion`; each underived component is `kernel.ι`. |
| The restriction arrow | `sectionHypercohomologyRestriction`, obtained by the same existing derived-transformation construction from `(sheafSections J A).map j.op`. |
| The boundary H^q(U,K) → H^{q+1}_Z(X,K) | A component of `δ i q : P.ι ⋙ sectionHypercohomologyFunctor ... q ⟶ P.ι ⋙ supportHypercohomologyFunctor ... (q + 1)`. Existence of one family over every pair is outside all the naturality quantifiers, so independently chosen incompatible boundaries do not satisfy the statement. |
| Long exactness | `SupportSequenceExact` asserts all three successive composites are zero and all three resulting `ShortComplex` objects are `.Exact`, for every coefficient object and every `q : ℤ`. Thus it includes exactness at H^q(X,K), H^q(U,K), and H^{q+1}_Z(X,K). |
| The ordinary sheaf sequence | Specialization to `DerivedCategory.Plus.singleFunctor _ 0`; the existing natural `Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso` identifies H^q(RΓ_Z(F[0])) with `(supportSections i).rightDerived q`, exactly `supportCohomology i q F`. The same comparison applies to terminal/open evaluation and to the canonical arrows. It recovers all natural-number degrees, including q = 0. Negative-degree vanishing for a degree-zero sheaf gives the usual initial zero term. |
| Bounded below, torsion cohomology | The domain is the full subcategory of `DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u+1})` selected by the existing `Scheme.HasTorsionEtaleCohomology`. There is no upper bound. Injective terms are not assumed torsion. |
| Functoriality in coefficients | The boundaries are natural transformations on that full subcategory. The first two arrows are already derived natural transformations. Thus every coefficient morphism commutes with all three arrows. |
| Functoriality in pairs | The second conjunct for each topology quantifies every `f : X' ⟶ X`, and arrows `t` and `s` from the terminal/open objects over X' to the actual base changes of the corresponding objects over X. The terminal arrow is unique; existence of s is exactly U' ⊆ f⁻¹U. The equality `s ≫ B.map j = j' ≫ t` is their restriction square. There is no morphism Z' → Z imposed on closed scheme structures and no requirement U' = f⁻¹U. |
| Compatibility with boundaries, choices, identities and composites for pairs | `SupportSequencePairNatural` quantifies every bounded-below termwise injective representative I,L, every specified isomorphism QI ≅ K, QL ≅ K', and every adjoint coefficient chain map b : I → f_*L. `supportPairComplexSectionMap` is explicitly evaluation of b followed by restriction along t or s. The map z of support complexes exists uniquely subject to its kernel-inclusion square and the displayed homology/boundary square. It is therefore the kernel map induced by those section maps, not an arbitrary map. `supportSequenceModelIso` uses the existing right-derived unit and the specified representative isomorphism, fixing the transport of δ. All representatives are covered. Homotopic choices give homotopic support maps, because their homotopy components satisfy the same restriction square and hence restrict to kernels; identical and composite adjoint chain maps give identical and composite section/kernel maps. These are the concrete representative formulation of the asserted functoriality on derived coefficients, with the identity and composition laws explained in proof Steps 6–7. |
| Small pro-etale site | `Scheme.ProEt.topology X`, and its actual objects/morphisms from Mathlib; no passage to etale-origin coefficients. |
| Finite-torsion coefficients | The second factor quantifies `(l : ℕ) [Fact l.Prime]`, a finite-dimensional field extension `(E : Type u) [Algebra (Padic l) E]`, `(n : ℕ) (_hn : 1 ≤ n)`. The coefficient category is `ModuleCat.{u+1} (ULift.{u+1} (Padic.coefficientExtensionRing l E n))`. These are the recorded quotient rings A_{E,n}, with the canonical ring and module universe lift. Every module sheaf is included; no finite-stalk or constructibility restriction is added. Since A_{E,n} is a finite ring, cohomology is automatically torsion, so the coefficient property is `⊤`. |
| Both pro-etale sheaves and bounded-below complexes | The same `DerivedCategory.Plus` assertion includes arbitrary such complexes. Its single-object specialization gives the sheaf case through the same existing comparison. |

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.SupportCohomology`: `CategoryTheory.Sheaf.supportedSectionsFunctor`, its additive instance, both `supportRestrictionArrow` declarations, and the etale/pro-etale `supportSections`, `supportCohomology`, `derivedSupportSections`, `supportHypercohomology` constructions. They are used unchanged. Server source was checked with `scompile.py --source` and agrees with the shared source.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: imports the recorded D, D⁺ and homology constructions. The abelian-coefficient case uses `DerivedCategory.Plus` and the existing abelian torsion-cohomology predicate.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: `AlgebraicGeometry.Scheme.HasTorsionEtaleCohomology`, built from `CategoryTheory.Sheaf.IsTorsion`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `Scheme.Etale.mk`, `Scheme.smallEtaleTopology`. Their signatures and topology definition were read. The scheme convention node fixes no additional declaration of its own; `Scheme`, `IsClosedImmersion`, and `i.openComplement.ι` have their recorded meanings.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` and Mathlib's pro-etale site: the recorded coefficient derived-category convention is imported through the support module. This theorem uses the support dependency's `Sheaf ... (ModuleCat Λ)` encoding throughout, the same encoding its pro-etale support cohomology accepts.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.coefficientExtensionRing` and `Padic.finite_coefficientExtensionRing`, from the already landed `def-weil-l-adic-coefficient-extension`. That node was added to `stmt_deps` to name the precise finite coefficient ring explicitly; no existing field other than `lean` and that allowed dependency addition changes.
- Mathlib: `sheafToPresheaf`, `evaluation`, `sheafSections`, `Functor.rightDerivedFunctorPlus`, `DerivedCategory.Plus.homologyFunctor`, `DerivedCategory.Plus.Q`, `HomologicalComplex.homologyFunctor`, `ObjectProperty.inverseImage` and `.FullSubcategory`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`: `Functor.rightDerivedFunctorPlusNatTrans`; `...PlusSingle`: `DerivedCategory.Plus.homologyFunctorObjQIso`, `Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso`. The comparison definitions are imported, not restated with unspecified data.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` and `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`: the exact published continuity instances used explicitly in the pair clauses. The generic sectionwise pushforward in the model clauses is definitionally the recorded f_*.

All available proof-dependency modules were imported, except the direct import of
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`. Importing it together with
`ProEtaleRestrictionInjectives` fails because its finite-coefficient pro-etale
API and the latter's legacy pro-etale API both declare
`AlgebraicGeometry.ProEtale.«term(_)_*[_]»`. This was tested with scompile and repaired
by removing that proof-only import. The theorem uses the common Mathlib continuous
pushforward directly, and both actual site base-change functors are specified.
The relevant inverse-image adjunction construction is not restated; Step 7 records
its use for representing maps. No live module or tool was edited.

Edge cases checked before writing and against the completed signature:
empty X and Z; Z = X and U empty; Z empty and U = X; nonreduced closed subscheme
structures with identical support; zero coefficients; q = 0 and arbitrary negative
integer degrees for complexes; complexes unbounded above; locally torsion sheaves
without a global annihilator; non-quasi-compact complements; identity pair maps;
proper inclusions U' ⊊ f⁻¹U; arbitrary scheme morphisms; n = 1. Level n = 0 is
excluded exactly by the positive-level finite coefficient convention. There is
no geometric-stalk, etale-descent, lisse, or constructibility hypothesis.

Searches (2026-10-16):

- `msearch.py ... leanfinder "long exact sequence cohomology with support open closed pair torsion etale sheaf"`: eight hits, including Mayer–Vietoris free-sheaf short complexes, group cohomology long exact sequences, and K-injective construction. None gives this support sequence or pair naturality.
- `msearch.py ... loogle "Sheaf, supportedSectionsFunctor, rightDerivedFunctorPlus"`: zero hits, unknown identifier `Sheaf` in the service index.
- `msearch.py ... leansearch "long exact sequence for cohomology with support in closed subset etale site"`: unavailable, Internal Server Error; no verdict drawn from this search.
- `msearch.py ... grep "support.*[Cc]ohomology|[Ss]upport.*[Ee]xact"`: unrelated ring/module supports and factorization supports; no site-support exact sequence.
- Direct `rg` in Mathlib's Sites and Algebra/Homology, the upstream `WeilConjectures` tree, and `lean/Sheaf`: no matching statement. `rg "thm-pur-with-support-exactness"` in upstream gives no declaration. Existing support definitions are exactly the dependency module, and the existing cohomological long exact sequences concern short exact sequences of coefficients or distinguished triangles, not this kernel-of-restriction functor. In particular `ShortComplex.ShortExact.exists_rightDerived_δ_exact` derives one functor on a coefficient short exact sequence, so it does not state the present theorem.
- All new declaration names were also searched directly in Mathlib, upstream and `lean/Sheaf`; no collision.

There are no new independent definition nodes, dependency repairs, statement
corrections, or `STATEMENT-DISPUTED` flags. Helper definitions only package the
canonical maps and exactness/naturality clauses belonging to this node, and are
all listed in `lean.declarations`. Universes and variables are explicit and
`autoImplicit` is disabled. Compilation and dry-run status are recorded below.

Validation: `scompile.py NL thm-pur-with-support-exactness lean/Sheaf/AlgebraicGeometry/SupportLongExact.lean` completed successfully for both the sandbox and library module, with no errors or warnings. The node signature matches the module verbatim, and no Lean line exceeds 100 characters.

## Second reading by NL

I read the item node, its proof steps, the support-cohomology dependency, and the
Milne Section 9 Theorem 9.4 source cited by the node. The statement list and verdicts
are as follows.

| Node object or clause | Lean rendering and verdict |
| --- | --- |
| Scheme `X` | The etale factor quantifies `{Z X : Scheme.{u}}`; no Noetherian, separated, quasi-compact, characteristic, or field hypothesis is added. **Matches.** |
| Closed subscheme `i : Z → X` | Every pair quantifier has `(i : Z ⟶ X) [IsClosedImmersion i]`; nilpotent closed structures remain allowed. **Matches.** |
| Open complement `j : U → X` | `Etale.supportRestrictionArrow i` and `ProEtale.supportRestrictionArrow i` use `i.openComplement.ι`, so the actual open complement is used. **Matches.** |
| Torsion etale sheaf `F` | `Etale.supportSequenceCoefficients X` is the existing `Scheme.HasTorsionEtaleCohomology` property restricted to `D⁺`; the degree-zero specialization covers torsion sheaves. **Matches.** |
| Supported, global, and open cohomology | `supportHypercohomologyFunctor`, `sectionHypercohomologyFunctor`, and the open evaluation object are derived functors, with the localization dependency identifying the latter with `H^q(U,j⁻¹K)`. **Matches.** |
| Three arrows and boundary | `supportHypercohomologyInclusion` is derived kernel inclusion, `sectionHypercohomologyRestriction` is derived restriction, and the existential `δ` has type `H^q(U,K) → H^{q+1}_Z(X,K)`. **Matches.** |
| Long exactness | `SupportSequenceExact` states zero composites and `.Exact` at all three consecutive terms for every `K` in the torsion full subcategory and every `q : ℤ`. **Matches; no degree or initial-term clause is lost.** |
| Coefficient functoriality | `δ` is a natural transformation on the full subcategory, so maps in `F` commute with all arrows. **Matches.** |
| Pair functoriality | The pair clause quantifies arbitrary `f : X' ⟶ X`, terminal/open arrows `t,s` over the pullbacks, and their restriction square. `SupportSequencePairNatural` gives the unique support-complex map and boundary square for every injective representative and coefficient chain map. Identity and composition follow from this uniqueness, as in proof steps 6–7. **Matches.** |
| Bounded-below complexes | `DerivedCategory.Plus` is used, with no upper bound; torsion is a property of cohomology, not injective terms. **Matches.** |
| Pro-etale assertion | The second conjunct quantifies every prime `l`, finite-dimensional `E/Padic l`, positive `n`, and uses `Scheme.ProEt.topology` with `ModuleCat` over the finite coefficient ring and its universe lift. It repeats exactness and pair naturality. **Matches.** |

Edge cases checked: `X` or `Z` empty; `Z = X` (empty open) and `Z = ∅` (full open); nonreduced closed subschemes; zero coefficients; `q = 0` and negative degrees; complexes unbounded above; locally torsion coefficients without a common annihilator; non-quasi-compact opens; identity and proper-subopen pair maps; and positive level `n = 1`. No case excluded by a hidden finiteness, nonemptiness, or characteristic assumption. Level `n=0` is excluded by the node's finite-level convention (`1 ≤ n`).

Searches were rerun with `msearch.py` (LeanFinder, Loogle, LeanSearch, and grep), and with `rg` over Mathlib, the upstream `WeilConjectures` tree, and `lean/Sheaf`. They found no existing long exact support statement or declaration named by this item. Existing support constructions are precisely those in `SupportCohomology.lean`; no duplicate notion was introduced. The pro-etale coefficient ring is the existing `def-weil-l-adic-coefficient-extension` dependency, added to `stmt_deps` so the ring used in the signature is named explicitly; its landed finiteness interface is imported by the module.

The only mismatch found was documentary: the first report did not contain the required
second-reading section. I added this section. The Lean file itself had no statement,
hypothesis, universe, edge-case, or declaration collision mismatch; its theorem
signature is verbatim equal to the node's `lean.statement`, and `scompile.py` succeeds.
