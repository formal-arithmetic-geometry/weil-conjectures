## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.internalHom_stability` in
`Sheaf.Paper.DetThmSfCtfStabilityInternalHom`, with one postponed theorem and real helper
constructions. The node statement, proof, proof dependencies and source remain unchanged.
It gains the definition dependency `def-sfb-locally-constant-perfect-complex`.

Clause-by-clause matching:

- The fixed prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The field is `(k : Type u) [Field k]`.
  `[Fact (ringChar k).Prime]` expresses positive prime characteristic, and
  `[Fact (ringChar k ≠ ℓ)]` expresses p ≠ ℓ; characteristic zero is excluded.
- `X.Over (Spec (.of k))` is the structural morphism. `LocallyOfFiniteType` together
  with `QuasiCompact` says finite type, and `IsSeparated` says separated. No perfection,
  algebraic closure, finite cardinality, or smoothness assumption is imposed on k or X.
- Λ is the condensed ring object on the coherent profinite site, with `MonObj` and
  `IsCommMonObj`. `_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ` is the recorded six-case
  coefficient predicate. Thus it retains finite commutative ℓ-power-torsion A, Zℓ, O_E,
  Qℓ, finite E, and the condensation of all continuous maps into Qbarℓ for the stated
  topology; no discrete replacement or derived completeness condition is introduced.
- `moduleDerived Λ X` is only an abbreviation for the existing unbounded derived category
  of internal Λ_X-modules. `dctfPred` transparently expands the exact property defining
  `ConstantModelConstructibleFiniteTor`: `constantModelBoundedConstructible` intersected
  with `DerivedCategory.finiteTorAmplitude`. `_hK` and `_hL` render both memberships.
- `internalHomObj Λ X K L` is `((derivedHom Λ X).obj (op K)).obj L`, the recorded ambient
  relative derived internal Hom. The first conjunct asserts its Dctf membership.
- The locally closed immersion is quantified with *every* open-then-closed factorization:
  S, Sbar, a, u, i, `hu : IsOpenImmersion u`, `hi : IsClosedImmersion i`, `a = u ≫ i`.
  These subschemes inherit the standing finite-type separated structure from X, so the
  formula does not add independent standing-scheme assumptions. The statement includes
  identity, open, closed, and empty immersions.
- `IsLocallyConstantPerfectComplex Λ S P` states precisely the local model convention:
  a pro-etale cover, a bounded complex F on the condensed point, degreewise finite-free
  retracts (finite projective scalar modules), and a derived isomorphism to the actual
  termwise point-pullback model. Differentals are selected on the point; arbitrary
  coefficient functions on a scheme chart are not admitted. The hG witness only equips
  the canonical functor with its zero-preservation proof, not with new data or choices.
- `locallyClosedExtension` is exactly the extension used by the recorded tensor-projection
  dependency: `(openImmersionLowerShriek Λ u).mapDerivedCategory` followed by
  `(lowerStar Λ i).rightDerivedFunctor`. Closed pushforward and open extension are exact,
  so this is the canonical derived presentation of the termwise i_*u_! of the node.
- For a^! the declaration `exists_localizingExceptionalAdjoint` supplies a right adjoint
  on the recorded `localizingClosureProEtale` full subcategories, not an arbitrary functor
  on the ambient categories. `localizingLocallyClosedExtension` restricts the actual
  extension using only a membership witness h. The existential G in the conclusion is
  bound by `Nonempty (localizingLocallyClosedExtension ... h ⊣ G)`. It therefore IS the
  exceptional inverse image, uniquely up to the adjunction-compatible isomorphism of
  sk-prop-sf-existence, transported along the immersion compactification identification.
  This is the standard choice-independent presentation of that existing notion: there
  is no additional hypothesis requesting an adjoint, and no arbitrary object H replaces
  a^!L. `N : Loc(X)` with `N.obj = L` supplies its precise argument. Membership follows
  from Dctf ⊆ Loc and adds no assumption on L.
- The first `Nonempty` isomorphism in the formula is
  `RHom_X(a_!P,L) ≅ (lowerStar Λ a).rightDerivedFunctor.obj (RHom_S(P,(G.obj N).obj))`.
  The second isomorphism is from that right-hand expression to
  `Ra_*(dualTensorObj Λ S P (G.obj N).obj)`.
- `dualTensorObj` uses the existing `relativeInternalHomDual (Mon.mk Λ) S P`, whose full
  definition is RHom(P, singleFunctor(0)(Mod.regular Λ_S)), and then the recorded
  `derivedTensor`. This renders both P^vee = RHom(P,Λ_S) and the final tensor clause.
- `internalHomGenerator` is exactly the class of objects isomorphic to an extension a_!P
  of the stated form. The final universally quantified K' is any Dctf object, independently
  of the initial K,L. It belongs to every replete triangulated object property containing
  these generators. This is the smallest replete triangulated subcategory, equivalently
  finite expressions in shifts and cones of finitely many generators. Zero is included
  by `IsTriangulated.ContainsZero`. There is no retract closure or infinite coproduct
  operation in this generation assertion. In particular Mathlib `triangEnvelope` was
  inspected and rejected because it explicitly adjoins retracts.

Recorded statement dependencies and declarations read and used:

- `sk-def-sfb-dc-setting`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and its scheme/base
  conventions. They are rendered by explicit standing binders, as that node's record says.
- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`; its public import
  `Sheaf.Paper.LocalizingClosure` supplies `localizingClosureProEtale` and its inclusion.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `constantModelBoundedConstructible`, `ConstantModelConstructibleFiniteTor` and the
  finite constant scalar presentation convention in `HasFiniteConstantLocalModel`.
- `sk-def-sfb-derived-tensor-hom`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`,
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedHom`, `derivedTensor`, and their relative
  tensor-Hom adjunction. This is Layer B over Λ_X throughout.
- `sk-prop-sf-existence`: `Sheaf.Paper.LocalizingExceptionalAdjoint`,
  `localizingLowerShriek`, `exists_localizingExceptionalAdjoint`, and the theorem's
  uniqueness clause for the adjunction-compatible right-adjoint isomorphism.
- `def-pc-perfect-ring-complex`: `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`,
  `DerivedCategory.IsPerfectRingComplex`, with independent localization universe.
- `def-weil-pbc-strict-perfect-coefficient-package`:
  `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`,
  `SheafOfModules.StrictPerfectCoefficientRepresentationOfUniverses` and the imported
  finite-free retract package. The new condition requires the scalar model on the point,
  rather than replacing it by arbitrary ringed-site perfectness.
- `det-lem-int-tensor-projection`: `Sheaf.SixFunctors.IntTensorProjection`,
  `locallyClosedImmersionTensorProjection`; the extension composite is precisely its
  existing one. No new extension-by-zero operation is invented.
- The new definition's existing constituents are
  `Sheaf.Paper.InternalHomDualTorAmplitude`,
  `AlgebraicGeometry.ProEtale.FiniteProjectiveCondensedModule`,
  `scalarExtensionComplex`, and `relativeInternalHomDual`. The cover predicate is the
  same inline hP condition of its `internalHom_dual_tor_amplitude` declaration.

The module publicly imports the statement dependency modules and non-publicly imports the
recorded proof dependencies that are stated. Mathlib leaf files are imported for their
recorded declarations, and the closed upstream geometric-stalk and proper-immersion
interfaces are imported too. The following proof-only nodes have no declaration yet and
are therefore omitted from imports: sk-lem-int-integral-heart,
det-pe-finite-tor-comparison-noetherian, det-lem-int-integral-heart-local-model,
det-thm-sf-ctf-stability-direct-images, def-sfb-dc-open-lower-shriek-adjunction,
lem-sfb-open-closed-internal-hom-formulas. The main docstring reproduces every node proof
step, with all of its cited nodes, for the subsequent proof worker.

Edge cases checked: zero coefficient ring and zero modules; rank-zero retracts; zero
complex; empty scheme and empty covering family; bounds varying with the cover member;
empty finite generation (zero object); negative and positive shifts; arbitrary morphisms
for cone formation; finite coefficients not necessarily fields; integral and rational
coefficient stages; arbitrary standing field with p ≠ ℓ. The whole construction uses
Scheme.{u}, coherent Profinite.{u}, Ab.{u+1} and the standard derived universes, without
identifying site object and morphism universes or shrinking scalar test categories.

Searches (the wrapper logs the exact queries): LeanFinder for "locally constant perfect
complex on a scheme pro etale condensed coefficient ring" returned discrete condensed-module
functors, not this condition. LeanSearch for "locally constant perfect complexes pulled back
from finite projective condensed scalar modules" likewise returned
`CondensedMod.LocallyConstant.functor`, `functorIsoDiscreteAux₁` and
`CompHausLike.LocallyConstantModule.functor_obj_val`; none addresses the general condensed
coefficient complex condition. Loogle `DerivedCategory, IsPerfectRingComplex, derivedHom`
returned no hit (unknown IsPerfectRingComplex), and `DerivedCategory, MonObj` returned
`OK 0 hit(s) | loogle: unknown identifier 'MonObj'`. Mathlib grep
`LocallyConstant.*Perfect|IsPerfectRingComplex` returned zero hits. Source/node searches
used `rg`, upstream `grep -rn` for the item's id, and
`python3 tools/blueprint_refs.py search 'locally constant perfect'` (one blueprint node,
this item). Searches in `lean/Sheaf` found the existing finite-projective and scalar-extension
helpers in InternalHomDualTorAmplitude, which are reused; no named combined cover predicate
or exact stability theorem was found. `dag/lean_names_upstream.json` was searched for the
new declaration names, without hits. `blueprint_refs.py ancestor` returns this item itself.

The existing repair note was read: it is a resolved stage-1 re-splitting note from
2026-10-17. The present node's expanded proof is retained verbatim, including its newly
separated model/duality/Tor dependencies. No released stage-2 interface repair is pending.
No STATEMENT-DISPUTED finding and no source correction.

Validation: both delivered files compiled cleanly through scompile.py, separately and in
dependency order, with no errors or non-sorry warnings. The final wrapper run also passed: LocallyConstantPerfectComplex 11.2 s and
DetThmSfCtfStabilityInternalHom 20.8 s (each separately, under its 60 s limit).

## Second reading by Q20

The dispatcher explicitly started this worker without a lead and forbids starting other
agents; it specifies that the maintainer independently reads the delivery. Accordingly no
independent-worker review is claimed here. A further self-check opened the node and both
files and checked every hypothesis and clause as mapped above. It caught and removed an
early overly broad substitute for local constant perfectness, an arbitrary-object substitute
for a^!L, and a retract-closed envelope in the generation clause. The final forms use the
existing point-model helpers, the adjunction specifying a^!, and replete triangulated
closure under finite shifts and cones. Independent approval remains the maintainer's review.

## New nodes

`def-sfb-locally-constant-perfect-complex` names the combined cover condition in the item's
coefficient-model convention. It introduces only the missing predicate; finite-free
retracts, point pullback, termwise complex mapping and derived restriction are reused from
lem-sfb-internal-hom-dual-tor-amplitude. Its source is the item's statement and the second
paragraph of its proof. The three kinds of Mathlib search, project and DAG grep, and blueprint
search found no existing named combined predicate or definition node. The model bounds may
vary with the cover member, and the condition handles the empty scheme. It is directly
cited by the item's stmt_deps. All of its definitions have real data and contain no sorry.
