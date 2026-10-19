## Worker report

The module `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` states two theorems,
`AlgebraicGeometry.ProEtale.isConstructibleModuleObject_serre_padicSubfield` and
`AlgebraicGeometry.ProEtale.isConstructibleModuleObject_serre_padicAlgCl`.
Each states kernel/cokernel closure and extension closure in the existing internal-module
category. Both proofs are `sorry`; no definition or categorical structure is introduced.
The node is unchanged except for `lean`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| A prime ℓ | `(ℓ : ℕ) [Fact ℓ.Prime]` in both theorems. |
| Fixed algebraic closure Ω of ℚ_ℓ | `PadicAlgCl ℓ`, Mathlib's abbreviation for `AlgebraicClosure ℚ_[ℓ]`; the framework uses this fixed choice, rather than a completed algebraic closure. |
| Scheme T | `(T : Scheme.{u})`. |
| Underlying space noetherian | `[TopologicalSpace.NoetherianSpace T]`; this does not require noetherian local rings. |
| Finite intermediate fields E | `(E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))`; definitionally the framework's `PadicAlgCl.FiniteIntermediateField ℓ`. |
| E_T^c = p_T^* C(-,E) | `padicSubfieldRingObj T ℓ E`, definitionally `condensedRingObj (Profinite.continuousMapRingObj E) T`. |
| Ω_T^c = p_T^* underline Ω, finite-field-valued continuous sections | `padicAlgClRingObj T ℓ`, using `Profinite.padicAlgClRingObj ℓ` and its bounded-image subfunctor, not all continuous maps into Ω. |
| Module sheaves over A | `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) A`, precisely the internal module category fixed in the condensed-category dependency. |
| Finite locally closed stratification with locally finitely presented restrictions | `IsConstructibleModuleObject A M`, whose definition uses a finite scheme stratification and `IsLocallyFinitelyPresented` after `upperStar.mapMod` along each immersion. |
| Local cokernel of a finite-rank free map | The latter predicate requires a `Scheme.Cover` and `Mod.IsFinitelyPresented` on every member; `Mod.IsFinitelyPresented` is existence of `m n : ℕ` and an isomorphism with `cokernel (f : finiteFree A m ⟶ finiteFree A n)`. |
| Morphism between constructible sheaves | Universal `M N` and `(f : M ⟶ N)`, followed by the two `IsConstructibleModuleObject` premises. |
| Constructible kernel and cokernel | First conjunct concludes the conjunction of `IsConstructibleModuleObject A (kernel f)` and the same assertion for `cokernel f`. |
| Every short exact sequence 0 → M → P → N → 0 | Universal `S : ShortComplex ...` and `S.ShortExact`; Mathlib defines this as exactness, mono first map, epi second map. |
| Constructible M and N imply constructible P | Second conjunct has constructibility premises on `S.X₁`, `S.X₃`, and conclusion on `S.X₂`. |
| Either finite E coefficients or Ω coefficients | The two declarations respectively give these identical clauses for the two coefficient choices. |
| No derived completeness imposed | All terms are ordinary module sheaves and local finite presentations; no completion predicate or derived category appears in either signature. |

The framework's `Scheme.Stratification` requires constructible locally closed parts.
This agrees with the node's locally closed stratification on a noetherian space:
`Scheme.Stratification.ofNoetherianSpace` supplies the extra condition automatically.
The recorded `Scheme.LocallyClosedStratification` extends the same finite topological
stratification and carries the same schemes, immersions and image equalities. Neither
requires reduced strata. No second stratification or constructibility notion is needed.

Dependency declarations read and used:

- `Mathlib.NumberTheory.Padics.PadicNumbers`: `Padic`; the completion of the rationals.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`; and
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`.
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`;
  specializes to the fixed closure used by the coefficient-ring framework.
- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`:
  `AlgebraicGeometry.ProEtale.IsConstructibleModuleObject` and
  `AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `pointUpperStar`, `upperStarFromPoint`, `condensedRingObj`, and coefficient comparisons.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`:
  `AlgebraicGeometry.ProEtale.padicSubfieldRingObj` and `padicAlgClRingObj`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`:
  `Profinite.continuousMapRingObj`; `...Condensed.EllAdic`:
  `Profinite.padicAlgClRingObj`, `padicAlgClSubfunctor`, `padicAlgClCondensedRing`.
- `WeilConjectures.CategoryTheory.ModuleObjects.Free`: `Mod.IsFinitelyPresented` and
  `Mod.finiteFree`, read to check the exact presentation condition.
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`:
  `Scheme.LocallyClosedStratification`; the finite stratification dependency.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is the
  transparent general-site `SheafOfModules` encoding. The more specific condensed-category
  dependency explicitly uses internal module objects, and those are used here without
  replacing them by a separate sectionwise module category.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- The size-convention node is metatheoretic; explicit `universe u`, `Scheme.{u}` and
  `Ab.{u + 1}` implement the published pro-etale framework's size convention.

The five available proof-dependency modules are imported non-publicly: site pullback exactness,
module-sheaf colimits/forgetfulness, the pro-etale site, common stratification refinement,
and finite common covering refinement. Other proof dependencies have no recorded modules;
no proof-only imports were invented. Both docstrings describe all seven natural-language
proof steps, including the two idempotent presentations and local basis lifts for extensions.

Edge cases checked: the empty scheme is allowed, as are empty strata, zero source or target,
zero morphisms, and presentations with m or n zero. No positive-rank, nonempty-stratum,
connectedness, separatedness, finite-type or characteristic restriction is introduced.
Only the underlying scheme space is noetherian; a pro-etale covering scheme need not be.
For an extension with zero-rank quotient, the empty list of lifts needs no refinement.
The coefficient topology is the inherited p-adic topology, and the algebraic-closure ring
uses sections landing in one finite intermediate field even on an infinite profinite set.

Searches for an existing statement:

- `msearch.py leanfinder`: "constructible condensed field module sheaves closed under kernels cokernels extensions" returned eight condensed-category results, none asserting constructible closure.
- `msearch.py loogle`: `CategoryTheory.ShortComplex.ShortExact` returned the exact short-exact-sequence predicate and its API; no specialized closure theorem.
- `msearch.py grep`: `IsConstructibleModuleObject|IsSerreClass` returned generic Serre-class infrastructure and an unrelated finite abelian-group example, no matching theorem.
- `msearch.py leansearch`: "constructible condensed field module sheaves closed under kernels cokernels and extensions" was unavailable (Internal Server Error).
- `rg` in upstream `WeilConjectures` and side `lean/Sheaf`: `IsConstructibleModuleObject|condensed.*[Ss]erre` found no matching closure statement. The newer framework supplies the definition; its `DerivedCategory.lean` explicitly calls the sheaf-closure assertion unformalized.
- `grep -rn` for the item id in upstream `WeilConjectures` returned no attachment.
- `rg` for the proposed declaration names in Mathlib, upstream names and source, and `lean/Sheaf` returned no collision.

No statement correction, new node, dependency module or disputed statement is needed.
Validation: `deliver2.py NV lem-weil-pbc-condensed-constructible-serre --no-push` printed
`OK (dry run)` for commit `c643ada8db`: the module compiles cleanly through the server-only
`scompile.py` backend, and preflight passes except for the independent second reading.
The initial compile identified a missing `open scoped CategoryTheory.Obj`; this was added
to enable the framework's existing ring-object instances. No mathematical statement changed.
Nothing was pushed. The independent second reader supplies their own reading and delivery.

## Second reading by NV

I independently opened the node, both delivered theorem signatures, every statement
dependency record and the relevant source declarations. The node's archived source
path is absent on this machine; I read the exact copied framework module
`lean/WeilConjectures/ConstructibleSheaf/ProEtaleModule/DerivedCategory.lean`
listed in `coord/pefw-upstream-framework.md`. Its “Sorried input” explicitly requires
only a topologically noetherian scheme for the sheaf closure input. I also read
Stacks `topology.tex`, definition-paritition (09XZ), and `sites-modules.tex`,
lemma-abelian-abelian (03CN) and lemma-pullback-module (03D2), including their
surrounding site hypotheses. They add no scheme finiteness or characteristic condition.

Object, hypothesis and conclusion checklist (each verdict: matches):

| Node item | Lean rendering and independent verdict |
| --- | --- |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` in both signatures; exactly primality. |
| A fixed algebraic closure of Q_ell | `PadicAlgCl ℓ`, read in Mathlib `NumberTheory/Padics/Complex.lean`, abbreviates `AlgebraicClosure ℚ_[ℓ]`; it fixes the closure used throughout the recorded coefficient-category framework. No completion is substituted. |
| Finite intermediate E | `E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)`; I opened its definition and `PadicAlgCl.FiniteIntermediateField`: both are the subtype of intermediate fields finite-dimensional over Q_ell. |
| Scheme T with noetherian underlying space | `(T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]`; no local-ring noetherianity or finite-type requirement. |
| E coefficient ring pulled back from continuous functions | `padicSubfieldRingObj T ℓ E`; its abbreviation is `condensedRingObj (Profinite.continuousMapRingObj E) T`. I followed `pointUpperStar` (Kan extension and sheafification), `upperStarFromPoint` (composition with scheme inverse image), and the coefficient construction in Basic.lean. |
| Omega coefficient ring with finite-field-valued sections | `padicAlgClRingObj T ℓ`; I read `padicAlgClSubfunctor`, `padicAlgClRingPresheaf`, and `finiteIntermediateFieldValued`. Their sections are continuous maps with all values in one finite intermediate field, exactly as required even on infinite profinite sets. |
| Ordinary module sheaves | `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) A`, the internal module category explicitly fixed by the more specific condensed-category dependency. The general `ringedSiteModules` dependency is sectionwise sheaves of modules; no second category is defined by this delivery. |
| Finite locally closed stratification | `IsConstructibleModuleObject A M` quantifies over `Scheme.Stratification T`. I read its fields and `Scheme.Stratification.ofNoetherianSpace`: the additional constructibility field is automatic under this theorem's hypothesis, while schemes, immersion maps and image equalities are retained. |
| Local finite cokernel presentations on every stratum | `IsConstructibleModuleObject` uses `upperStar.mapMod` along the stratum immersion and `IsLocallyFinitelyPresented`; the latter uses a pro-etale `Scheme.Cover` and `Mod.IsFinitelyPresented`. I opened Free.lean: the last predicate is an isomorphism to a cokernel between `finiteFree A m` and `finiteFree A n`, with natural-number ranks. |
| Any morphism of constructible modules | First conjunct universally quantifies `M N` and `f : M ⟶ N`, then assumes precisely constructibility of both. |
| Constructible kernel and cokernel | The first conjunct concludes `IsConstructibleModuleObject A (kernel f) ∧ IsConstructibleModuleObject A (cokernel f)`. Both clauses are present. |
| Any short exact sequence | Second conjunct universally quantifies `S : ShortComplex ...` with `S.ShortExact`. I read Mathlib's structure: exactness, mono first arrow, epi second arrow. This is precisely the displayed sequence with endpoint zeros. |
| Constructible outer terms imply constructible middle | Premises are constructibility of `S.X₁`, `S.X₃`; conclusion is constructibility of `S.X₂`. No assumption on the middle term. |
| Both choices of coefficients | The Subfield theorem includes arbitrary finite E; the AlgCl theorem supplies all the same clauses for Omega. Together they cover the node's disjunction of coefficient choices. |
| No derived completeness | Neither signature uses a derived category or completeness predicate; constructibility is the existing ordinary finite-presentation definition. |
| Size convention | Explicit `universe u`, `Scheme.{u}`, and `Ab.{u + 1}` match the recorded framework. The fixed coefficient fields are small and lifted by the coefficient construction; no test-object quantifier is in an independent smaller universe. |

Edge cases: no nonempty or positive-rank assumptions occur. Empty schemes and empty
strata are admitted; `Fin 0` allows an empty partition when the space is empty.
`Mod.IsFinitelyPresented` allows either rank to be zero. Zero objects, zero maps,
and extensions with a zero outer term are included by the universal quantifiers.
The prime is unrestricted, including 2; the scheme's characteristic is unrestricted.
No noetherianity is imposed on objects of a pro-etale covering. The chosen algebraic
closure, rather than its completion, agrees with the dependency's fixed convention.

Independent searches, using terms different from the worker's first query:

- `msearch.py leanfinder "Serre subcategory constructible pro etale module finite presentation"`
  returned general `SheafOfModules.IsFinitePresentation` and solid condensed modules,
  not this closure statement.
- `msearch.py loogle "IsSerreClass"` reported an unknown unqualified identifier.
  I therefore also opened Mathlib's SerreClass sources by `rg`: they supply generic
  object-property infrastructure, no specialized constructible coefficient result.
- `msearch.py leansearch "Constructible sheaves of modules on the pro-etale site are closed under kernels and extensions"`
  was unavailable with Internal Server Error; no absence conclusion is drawn from it.
- `msearch.py grep "IsConstructibleModuleObject|isConstructibleModuleObject_serre"`
  found no upstream match through that service. Direct `rg` over the full upstream
  WeilConjectures tree, the copied framework and project `lean/Sheaf` located the
  constructibility definitions and the unformalized input in DerivedCategory.lean.
  I opened the nearby candidates `ConstructibleSheaf/KernelCokernel.lean` and
  `CategoryTheory/DerivedCategory/Constructible.lean`: those statements concern
  small-etale sheaves with discrete ModuleCat coefficients, not the internal modules
  over these condensed coefficient sheaves. They cannot replace this item.

I found no mathematical mismatch and changed no Lean or node statement. The report's
sentence that the recorded LocallyClosedStratification has only locally closed fields
needs a qualification: in the current framework its inherited Topology.Stratification
also carries constructibility. This causes no restriction here, by the noetherian
constructor read above. There are no new nodes, dependency modules, statement
corrections or citer verdicts to review in this delivery.

Both theorem docstrings carry the source and blueprint id and follow all seven proof
steps: exact restriction and cover base change; scheme-theoretic common refinement;
local triviality only on noetherian strata; cokernel and image presentations; the
kernel presentation as coker(tp); extension splitting by local basis lifts; and
assembly on the finite stratification. Both proofs remain wholly `sorry`; no definition,
instance, private notion, or proved auxiliary result was added. All variables and the
single universe are explicitly bound. The recorded primary signature agrees verbatim
with the normalized signature read from the file; the second theorem is listed in
`lean.declarations` and supplies the remaining coefficient case.

Independent validation: server-only `scompile.py` passed with no warnings or errors.
The delivered module took 2.0 seconds; every side-only import also passed within
60 seconds, with nice 19 and two threads. No source or signature repair was needed.
