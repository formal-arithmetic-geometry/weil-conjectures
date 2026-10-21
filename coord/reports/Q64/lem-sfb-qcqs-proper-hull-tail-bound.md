## Worker report

The module `Sheaf.Paper.QcqsProperHullTailBound` states
`AlgebraicGeometry.ProEtale.CondensedRing.exists_uniform_lowerTail_bound_of_isProper`.
Its only theorem proof is `sorry`. No definitions, new nodes, dependency repairs, or
statement corrections were needed. The target node's other fields are unchanged.

Hypothesis and clause correspondence:

- The fixed prime is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The commutative condensed coefficient ring is
  `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ]`. The admissibility hypothesis is
  `hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ`, precisely the recorded coefficient
  convention of sk-def-localizing-closure. That predicate supplies the finite discrete
  ℓ-power-torsion rings, ℤ_ℓ, ℚ_ℓ, finite extensions inside the fixed PadicAlgCl and their
  integer rings, and the algebraic-closure cases of the dependency's current interface.
  A finite extension is selected inside that predicate when it is the coefficient case;
  no unrelated extra extension is required for the other cases.
- The size convention is the explicit universe `u`, `Scheme.{u}`, the small
  `Scheme.ProEt.topology` sites and coefficient groups in `Ab.{u + 1}`. The ambient
  module-object derived category and the localizing closure use the dependency's
  existing universe-polymorphic constructions. No equality between independently
  specified site object and morphism universes is introduced.
- The base is `{S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]`.
- The proper structure map and proper map in the node are `(q : Y ⟶ S) [IsProper q]`
  and `(f : X ⟶ Y) [IsProper f]`. Properness already supplies finite type; no additional
  field, characteristic, Noetherian, separated-base or finite-dimensional hypothesis
  is imposed.
- `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)` is
  Mod_{Λ_X}, with Λ_X the existing canonical pullback of the condensed coefficient ring.
  `K : DerivedCategory (...)` is an ordinary unbounded ambient module-object complex.
- `localizingClosureProEtale Λ X K` is membership in the intersection of full replete
  triangulated ambient subcategories closed under small sums and containing the
  bounded finite constant-model constructible finite-Tor objects. Its body uses
  `constantModelBoundedConstructible Λ X ⊓ fun K ↦ DerivedCategory.finiteTorAmplitude _ K`;
  hence it uses the node's exact generators rather than the older arbitrary-matrix
  constructibility convention.
- `∃ c : ℕ, ∀ (a : ℤ) (K : DerivedCategory ...), ...` chooses the bound before both
  cutoff and object, making independence of a and K literal. The fixed morphisms and
  coefficient data precede this existential.
- The lower tail is `(DerivedCategory.TStructure.t.truncLE (a - 1)).obj K`, the
  canonical good truncation τ_{≤a-1}, including the boundary kernel. It is not a
  stupid truncation and is applied in the ambient derived category. The hull
  hypothesis is on K only, with no hull-membership or completeness premise on its tail.
- The image is `(moduleObjectDerivedPushforward Λ f).obj (...)`, whose body is the
  total right derived functor of the full underived `lowerStar Λ f` composite, not a
  separately derived abelian-sheaf functor or derived-completed image.
- `∀ r : ℤ, a + (c : ℤ) ≤ r → IsZero ((DerivedCategory.homologyFunctor _ r).obj ...)`
  is exactly H^r(Rf_* τ_{<a} K) = 0 for r ≥ a+c. Homology is valued in the module-object
  category, so `IsZero` expresses zero cohomology, not subsingletonness of a bare type.

Dependency declarations read and reused:

- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`; its public import
  `Sheaf.Paper.LocalizingClosure` supplies
  `AlgebraicGeometry.ProEtale.localizingClosureProEtale` and
  `CategoryTheory.localizingClosure`, read in full.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`, read with
  its section binders and its full body `(lowerStar Λ f).rightDerivedFunctor`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `IsConstantModelConstructible`, `constantModelBoundedConstructible` and
  `ConstantModelConstructibleFiniteTor`, including finite constant local models and
  finite constructible stratifications. They are publicly imported and used by the hull.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`, available through
  the properness import; their defining fields were read.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`, and its underlying-scheme `QuasiSeparatedSpace`
  formulation. `Mathlib.Topology.Defs.Filter`: `CompactSpace`, read at its declaration.
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`: the recorded aggregate
  interface for def-kun-truncations. Its documentation specifies standard derived
  truncation as `DerivedCategory.TStructure.t`. The Mathlib definitions of this
  t-structure and `Triangulated.TStructure.truncLE` were read; the homotopy-colimit
  predicate itself is not substituted for truncation.
- `def-weil-size-convention` is explicitly a metatheoretic convention with no
  declaration or module, implemented by the universes above.

All already-stated proof dependencies are imported without `public` unless also a
statement dependency. In particular this includes the module-object Grothendieck and
K-injective interfaces, derived-coproduct colimit theorem, long exact cohomology sequence,
triangulated right-derived functor, bounded heart-amplitude dévissage, and ordinary
Postnikov–Roos module. The unrecorded geometric heart estimate remains a proof dependency;
it is not assumed as an additional hypothesis. The docstring carries all five node proof
steps, including the extra Milnor degree absorbed in c=d+1.

Edge cases read against the signature: K may be zero, unbounded in either direction,
or any shift of a generator; a and r are unrestricted integers (including negative and
zero). The condition on r includes equality r=a+c. The natural number c can be zero.
Empty schemes and empty fibres are admitted; neither a point nor a nonemptiness instance
is required. Finite coefficient rings may be zero. No invertibility of ℓ on the base,
field assumption, Noetherian hypothesis or completeness condition has been inserted.
Truncation is unrestricted even when it leaves the hull. No counterexample or typing
fault was found; no STATEMENT-DISPUTED flag is asserted.

Searches actually performed using the prescribed msearch.py wrapper:

- leansearch: “Uniform cohomological bound for proper pushforward of lower truncation
  tails in the constructible finite Tor localizing hull”. Eight hits, for general
  truncation and support constructions, e.g. TStructure.truncGE, CochainComplex.truncLE
  and ιTruncLE; none is this geometric bound.
- leanfinder: “Uniform upper cohomology bound for derived proper pushforward of lower
  truncations on a quasi compact quasi separated scheme”. Eight hits, for qcqs section
  lemmas and affine limit sections, including exists_of_res_zero_of_qcqs; no match.
- loogle: `AlgebraicGeometry.IsProper, DerivedCategory.IsLE`. Zero hits.
- grep: `proper.*(trunc|amplitude|bound)|lowerTail|trunc.*proper`. Twenty-five hits in
  Mathlib, chiefly unrelated order, topology, and truncation files; no match.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` with
  `hull_tail|lowerTail|proper.*(trunc|amplitude|bound)|trunc.*proper`, and direct grep of
  the node id in `lean/WeilConjectures`. No node-id binding or exact matching theorem.
  Related finite proper classical amplitude theorems concern finite coefficients and
  classical objects. The upstream ProperLowerStarCoproducts module was opened: its
  generic theorem assumes a heart bound and concerns an older bounded-constructible
  hull, so it does not itself state this theorem. The chosen full declaration name was
  also searched in Mathlib's project consumers, both project source roots and
  dag/lean_names_upstream.json, with no collision.

Validation: scompile.py compiled both the sandbox and real module artifact cleanly
(4.1 s and 12.5 s). The initial missing CategoryTheory.Obj scope was repaired with the
same scoped instance import used in the recorded derived-pushpull module. There are no
remaining compiler errors or warnings and no lines longer than 100 characters.

## Second reading by Q64

This is the author's separate second pass under the dispatcher's direct-delivery brief;
independent review belongs to the maintainer. I reopened the node and the final module
and matched the explicit ℓ, coefficient ring, admissibility predicate, qcqs S, proper q
and f, ambient K, hull membership, and the exact ≥a+c cohomology conclusion. I unfolded
the recorded hull's definition to verify finite constant-model generators and ambient
coproducts, and read the recorded derived-pushforward body to exclude a completed or
factorwise derived replacement. I checked τ_{≤a-1} and its sign against Mathlib's
canonical t-structure truncLE definition. The quantifier order supplies a single c before
a and K, and there is no assumption on the truncated object's membership or completeness.
No statement mismatch was found and no node statement or dependency list was changed.
The only elaboration repair was opening the dependency's existing CategoryTheory.Obj
scope; it adds no hypothesis or construction. The final signature was copied verbatim
into lean.statement, and every original node field other than lean is preserved.
