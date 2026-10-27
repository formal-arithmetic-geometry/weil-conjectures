## Worker report

The module `Sheaf.Paper.QcqsIntegralScalarExtensionCTF` states
`AlgebraicGeometry.ProEtale.CondensedRing.qcqs_integral_scalar_extension_ctf`, with its
sole proof `sorry`. No statement correction or additional node is needed. The node copy
changes only `lean`.

Hypotheses and clauses, read against the node and the complete Lean definitions:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The standard algebraic closure is
  `PadicAlgCl ℓ`. `F : PadicAlgCl.FiniteIntermediateField ℓ` is exactly an intermediate
  field with finite dimension over `ℚ_[ℓ]`; its subtype includes the finiteness proof.
  The algebraic closure is fixed in the node, and the existing recorded condensed-ring
  definition uses this standard closure. This is the same coefficient model as its
  dependencies, not a completeness hypothesis on a complex or on a scheme.
- In the finite-field case the node's family is the singleton `{E}`: use `F = E`.
  The first conjunct has coefficient `Profinite.continuousMapRingObj F` and the
  actual map `integralScalarMap ℓ F`. In the algebraic-closure case, the second
  conjunct holds for every finite subfield F; it uses
  `Profinite.padicAlgClRingObj ℓ`, with sections valued in one finite subextension,
  and the actual composite
  `integralScalarMap ℓ F ≫ Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F`.
  Thus the two allowed choices of Λ, and exactly their specified families, are covered.
- `integralCoeff ℓ F` is the continuous coefficient ring of `continuousIntegers ℓ F`,
  the unit ball of the restricted norm on F. Its topology is the subtype topology.
  This is O_F with the norm topology, rather than a discrete ring or an adic completion.
  Read the finite-extension coefficient definitions and `PadicAlgCl.integers` as well:
  they describe the same norm valuation ring; no second integral-ring construction is added.
- `T : Scheme.{u}` has `[CompactSpace T] [QuasiSeparatedSpace T]`, precisely qcqs.
  Mathlib's scheme quasi-separated class is quasi-compactness of the diagonal and is
  equivalent to this topological condition (Morphisms/QuasiSeparated.lean:239).
- Every coefficient ring on T is `condensedRingObj ... T`, the recorded pullback from
  the profinite point, and every coefficient map is `coefficientMap φ T`.
  The modules are `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ...`, using
  Mathlib's actual action-compatible internal module objects and the small pro-etale
  site. Schemes have universe u, small-site objects u+1 and morphisms u, abelian
  coefficients u+1, and the ordinary derived categories are formed in the corresponding
  larger universe. No object/morphism universe equality is assumed.
- `IntegralScalarExtensionCTF` quantifies `h : PreservesFiniteLimits
  (Mod.extendScalars (coefficientMap φ T))`, stating flatness of the specified inclusion.
  Its `PreservesFiniteColimits` clause states right exactness, so together these are
  exact ordinary scalar extension. The flatness witness is an existential conclusion,
  not an extra hypothesis on the theorem.
- `integralCTFDerived a` has body exactly `(Mod.extendScalars a).leftDerivedFunctor`.
  `integralCTFCounit a` has body exactly its existing `leftDerivedFunctorCounit`.
  `IsIso (integralCTFCounit (coefficientMap φ T))` gives the canonical termwise
  description on every homotopy complex and hence the ordinary derived factorization.
  This is a statement about the specified canonical counit, not an arbitrarily chosen map.
- `integralCTFShift a h` is `Functor.CommShift.ofIso` of the canonical comparison
  with the exact termwise functor. The explicit `@Functor.IsTriangulated` clause
  uses this shift structure; it does not merely ask for some unrelated shift structure.
  The `letI` in the definition's real construction installs the conclusion witness h;
  there are no let binders or hidden assumptions in the theorem statement.
- For every integer q, the `Nonempty` natural-isomorphism clause is an isomorphism
  between functors on the entire unbounded derived category:
  `integralCTFDerived ... ⋙ DerivedCategory.homologyFunctor _ q` and
  `DerivedCategory.homologyFunctor _ q ⋙ Mod.extendScalars ...`.
  It therefore says H^q(T_F,T J) ≅ Λ_T tensor H^q(J), naturally in every J.
- `J : ConstantModelConstructibleFiniteTor A T` is the dependency's full subcategory
  of bounded finite-constant-model constructible objects of finite Tor amplitude.
  For *each* `a b : ℤ`, the hypothesis `DerivedCategory.torAmplitudeIn _ a b J.obj`
  implies membership of the extended object in
  `constantModelBoundedConstructible Λ T ⊓ DerivedCategory.finiteTorAmplitude _`,
  and `DerivedCategory.torAmplitudeIn _ a b` for that object. Both D_ctf membership
  and exactly the original Tor interval are retained.
- The final clause quantifies every q, `S : Scheme.Stratification T`, and
  `s : Fin S.n`. Its premise is precisely
  `HasFiniteConstantLocalModel A (S.domain s)` of the restriction of H^q(J).
  It concludes a pro-etale cover of that *same* stratum and `Mod.IsFree` on each member
  of the cover for the restriction of H^q(T_F,T J). `Mod.IsFree` is an isomorphism
  with `Mod.finiteFree ... n` for some natural n, including zero. This is local finite
  freeness, rather than arbitrary finite presentation over local coefficient functions.
- The relative tensors in the finite-Tor predicates are the module-object derived
  monoidal structures of the recorded dependency. No completed, solid or derived-complete
  category, no Noetherianity, and no invertibility of ℓ on T is imposed.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` exports the recorded
  `Padic.finite_coefficientExtensionRing` and the finite extension degree, absolute-value,
  integer and quotient constructions. The present statement only needs the finite
  intermediate field and norm valuation-ring part of this coefficient datum.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` supplies
  `Profinite.padicAlgClCondensedRing` / `Profinite.padicAlgClRingObj`, read including
  the finite-subextension-valued section definition. `...Condensed.FiniteSubextension`
  supplies the actual `Profinite.padicSubfieldRingObjToPadicAlgCl` inclusion.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` supplies `coefficientRing`
  and `condensedRingObj`, with transported unit, multiplication and commutativity.
- `Mathlib.CategoryTheory.Monoidal.Mod` supplies `CategoryTheory.Mod`, its action,
  unitality and associativity axioms, and action-compatible morphisms.
- `Sheaf.Paper.CondensedModuleDerivedPushpull` exports the ordinary unbounded derived
  framework for these module objects (`moduleObjectDerivedPushforward` and
  `moduleObjectDerivedPullback`); it is a statement dependency import.
- `def-weil-size-convention` is metatheoretic; it has no Lean definiendum. Its explicit
  universe convention is implemented by the universes above, not an extra axiom.
- `Sheaf.Paper.CondensedConstantConstructibility` supplies
  `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`,
  `IsConstantModelConstructible`, `constantModelBoundedConstructible`, and
  `ConstantModelConstructibleFiniteTor`. Their full definitions were read. In particular,
  presentations are chosen on the profinite point before pullback, and the stratification
  is finite constructible locally closed, as the item requires.
- `Mathlib.Topology.Defs.Filter.CompactSpace` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated.QuasiSeparated` give the
  two qcqs notions, with the latter expressed on a scheme by `QuasiSeparatedSpace`.
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars` supplies
  `Mod.derivedExtendMapDerivedCategoryAdjunction`, `Mod.preservesKFlatQuasiIso`,
  the exact restriction instances and the generic `Functor.leftDerivedFunctor` /
  `leftDerivedFunctorCounit` computation. Their signatures and docstrings were read.
  The local helpers name these exact constructions, without a replacement definition.

All recorded proof-dependency modules that are stated are imported, with private
`import` visibility when used only for the planned proof. The seven numbered proof
steps are written in the theorem docstring, including the internal/section equivalence,
canonical tensors, K-flat resolution, cancellation, and reflection of vanishing.
Mathlib proof leaves are imported from their recorded source modules. No proof import
was omitted for an import cycle.

Edge cases checked before drafting and in the second reading:

- Empty T, empty stratification and empty cover index: no nonemptiness is demanded;
  the local conclusions are vacuous where appropriate, and zero coefficients/modules
  on the empty topos cause no excluded case.
- The zero complex, zero scalar module and zero local rank: `Mod.IsFree` permits
  n=0. A finite torsion scalar module rationalizes to the zero model, as required.
- Free modules, torsion modules and their finite mixtures: rationalization gives the
  expected free rank and kills the torsion, so local finite presentation is not being
  confused with local freeness before extension.
- F=ℚ_ℓ (the bottom finite subfield) and F itself as the finite coefficient target are
  included. The algebraic-closure case uses any finite F, with no finite-degree bound.
- Any q and any integer interval, including a=b and a>b: no bound/order is added.
  An empty interval only applies when the Tor test already vanishes, and is retained.
- General qcqs non-Noetherian T, including residual characteristic ℓ, is admitted.
  The finite locally closed strata are not treated as objects of T's pro-etale site:
  the recorded coefficient pullback to each scheme stratum is used.

Searches actually run:

- msearch leanfinder: `Integral to rational condensed coefficient extension preserves
  finite constant constructibility and Tor amplitude`. Eight hits concerned condensed
  modules/solidness, not this assertion.
- msearch loogle: `"extendScalars", "PreservesFiniteLimits"`. One hit:
  `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`, for ordinary scalar modules;
  it does not state the module-object finite-model or Tor-interval assertions.
- msearch grep: `integral.*scalar|scalar.*constructible|extendScalars.*torAmplitude`.
  Twenty-five hits were unrelated ordinary algebra/integration statements.
- msearch leansearch: `Flat scalar extension of sheaves preserves constructibility and
  Tor amplitude`. Eight hits were ordinary flat base-change lemmas, not this statement.
- rg on `lean/WeilConjectures` and `lean/Sheaf`, and by the exact item id, found no
  existing declaration of the item. Targeted searches for `HasFiniteConstantLocalModel`,
  integral scalar maps, `IsLocallyFree|IsLisse|IsLocallyFiniteFree|LocallyFree`,
  `torAmplitude`, and derived scalar-extension names located the dependency APIs above.
  Searches for all five proposed full declaration names in both roots and
  `dag/lean_names_upstream.json` found no collision.

The source PDF's Theorem 7.7 and its surrounding §7.2 were read with pdftotext, as were
`det-sf-comp-coherence-cocycle.md` and its proof in main-20261015. The node already
explicitly distinguishes its finite-model claim from the derived-lisse comparison
of that paper; the Lean follows the node's ordinary finite-model statement exactly.
No STATEMENT-DISPUTED issue was found.

Validation: all compilation used the prescribed scompile.py wrapper. Initial direct
elaboration timed out; naming the generic derived construction and its canonical counit
before specialization resolved it. A successful full compile identified one class-definition
reducibility warning; the recommended `@[instance_reducible]` annotation was added to
`integralCTFShift`. The final clean compile and delivery preflight are recorded by the tools.

## Second reading by Q06

A fresh second pass by the same dispatched worker reread the node, the module and
its dependency definitions. No other agent was started, as this dispatcher brief
requires; the maintainer's independent review follows delivery.

The pass checked the prime and finite-subfield binders; norm-topological O_F;
the singleton finite-field case and all-F closure case; qcqs; pulled-back coefficients;
ordinary unbounded module-derived categories; flatness and exactness; the *canonical*
counit's invertibility; the canonical transported shift used for triangulation; natural
cohomology for every J and q; both D_ctf and exactly [a,b]; and local finite freeness
on each original stratum. The packaged proposition was expanded while checking:
none of its hypotheses is an added assumption on the theorem. Every definition
has real data, every universe is explicitly bound, and the only postponed proof is
the named theorem for this DAG node. No dependency's record needed repair.

The first draft wrote `IsTriangulated` without explicitly providing its required shift
structure. The revised statement specifies the canonical shifts transported from the
exact termwise functor via `integralCTFShift`, and checks `@Functor.IsTriangulated`
with that structure. This is the substantive correction found during drafting;
there is no change to the node statement. The final pass also checked zero rank,
empty schemes/strata and empty Tor intervals, and checked that the natural isomorphism
is at functor level rather than merely objectwise. All public helper declarations
belong to this item's assertion and are listed in `lean.declarations`.
