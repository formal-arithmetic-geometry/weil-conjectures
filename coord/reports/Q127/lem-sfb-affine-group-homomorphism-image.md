## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.AffineHomRationalPoints states
AlgebraicGeometry.affineGroupHom_faithfullyFlat_iff_surjective_points, with its only
proof `sorry`. No definitions, new nodes, dependency repairs or statement corrections.
The source is Milne, Algebraic Groups (2017), Proposition 5.47, printed p.110
(PDF page 122), specialized exactly as the node to an algebraically closed base
field and affine groups. I read that proposition and the image theorem 5.39.

Clause-by-clause rendering:

- The algebraically closed field is `(F : Type u) [Field F] [IsAlgClosed F]`.
- The F-group schemes are `(H₁ H₂ : Over (Spec (.of F))) [GrpObj H₁] [GrpObj H₂]`.
  This uses the recorded group-object interface, including its multiplication,
  identity and inverse laws; no commutativity is imposed.
- Affineness is `[IsAffine H₁.left] [IsAffine H₂.left]`.
- Finite type is `[LocallyOfFiniteType H₁.hom] [QuasiCompact H₁.hom]` and
  `[LocallyOfFiniteType H₂.hom] [QuasiCompact H₂.hom]`, exactly the recorded
  conjunction of local finite type and quasi-compactness for each structure map.
- Target smoothness is `[Smooth H₂.hom]`. There is no smoothness or reducedness
  assumption on H₁.
- The group homomorphism is `(f : H₁ ⟶ H₂) [IsMonHom f]`. The Over morphism
  includes compatibility with the F-structure map.
- Faithful flatness is `f.left.appTop.hom.FaithfullyFlat`: appTop is the actual
  induced coordinate-ring homomorphism F[H₂] → F[H₁]. RingHom.FaithfullyFlat
  supplies its induced algebra structure and uses Module.FaithfullyFlat, so this
  means faithful flatness of this coordinate-ring module, as specified by the node.
- An F-point is `Over.mk (𝟙 (Spec (.of F))) ⟶ H₁`; composition `x ≫ f` is the
  canonical map to H₂(F). `Function.Surjective` states its surjectivity. Since f
  is IsMonHom, it is also the underlying function of the induced group homomorphism.
- `↔` renders both directions of the node, with no extra conclusion.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: Field (def-weil-field).
- Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed, the algebraically closed
  clause recorded by def-weil-algebraic-closure; no algebraic closure construction
  or algebraic extension datum is required for this already closed field.
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj, and
  Mathlib.CategoryTheory.Monoidal.Mon: CategoryTheory.IsMonHom; the specialization
  to Over (Spec F) is documented and provided by the imported
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs (def-sc-group-scheme).
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme; and
  Mathlib.AlgebraicGeometry.AffineScheme: AlgebraicGeometry.IsAffine (def-pc-scheme).
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType, and
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact
  (def-weil-finite-type-morphism).
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth
  (def-sbc-smooth-morphisms).
- Mathlib.RingTheory.RingHom.FaithfullyFlat: RingHom.FaithfullyFlat, which imports
  Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra and its
  PrimeSpectrum.comap_surjective_of_faithfullyFlat
  (lem-weil-pbc-faithfully-flat-surjective-spectrum).
- WeilConjectures.Mathlib.RingTheory.Nullstellensatz:
  exists_algHom_ker_eq_of_isMaximal and eq_zero_of_forall_algHom_apply_eq_zero
  (lem-wf-affine-nullstellensatz-vanishing, whose partial record names these).
- WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced:
  AlgebraicGeometry.Smooth.geometricallyReduced (sbc-lem-smooth-geometrically-reduced).
- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsReduced
  (def-pc-reduced-scheme), available through existing imports.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  AlgebraicGeometry.IsClosedImmersion (def-weil-closed-immersion), publicly
  imported by GroupScheme.Defs.
- lem-sfb-affine-homomorphism-flat-image has no Lean record or mathlib_match at
  this reading, so there is no proof-module import to add yet. It is a proof
  dependency only, not a notion needed to type this statement. The proof docstring
  records its exact role for stage 3 and the maintainer's later import update.

Edge cases checked mathematically before writing: identity and maps to the
trivial group satisfy the equivalence. A group scheme has an identity section,
so an empty source is not an omitted possible case. In characteristic p,
Frobenius on the additive group is faithfully flat and surjective on points,
although not an isomorphism. The nonreduced source α_p mapping to the trivial
group is allowed and faithfully flat. The inclusion of the trivial group into
α_p would be surjective on points without faithful flatness: its target is not
smooth, explaining the necessary target hypothesis. No characteristic or
connectedness restriction occurs. Explicit universe u covers arbitrary field
and scheme size; there is no separately undersized test-algebra quantifier.

Searches performed with the prescribed msearch.py wrapper:

- leanfinder: "A homomorphism of affine finite type group schemes over an
  algebraically closed field with smooth target is faithfully flat if and only
  if surjective on rational points". Eight hits; the closest was
  AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine,
  which concerns surjectivity on all underlying scheme points and assumes
  flatness, and does not assert this rational-point criterion.
- loogle: "IsMonHom, FaithfullyFlat" returned no hits (unknown unqualified
  IsMonHom). Repeated with "RingHom.FaithfullyFlat": twelve hits, consisting of
  faithful flatness definitions, stability, spectrum and scalar-extension facts;
  no group-scheme rational-point criterion.
- grep through msearch, AlgebraicGeometry: pattern
  `faithfullyFlat.*[Pp]oint|[Ss]urjective.*[Gg]roup|[Gg]roup.*[Ff]aithfullyFlat`
  returned zero hits.
- rg in both live source roots lean/WeilConjectures and lean/Sheaf, for the node
  id and `faithfullyFlat_iff_surjective_points|faithfullyFlat.*[Pp]oints`, found
  no existing statement. Broader faithful-flat/surjective searches found only
  spectrum and scheme-morphism results. The proposed declaration name is absent
  from Mathlib and both project roots.

The inherited BLOCKED ending concerned a stage-1 reviewed-split gate. The current
brief-stage2.md §0 explicitly permits the stage-2 handoff; the current queue lists
this node in stage 2 and the node has no Lean record. The accepted split is copied
unchanged; only lean is added.

Validation: scompile.py Q127 lem-sfb-affine-group-homomorphism-image compiled both
the sandbox module and library-path module cleanly (9.0 s and 10.0 s).

## Second reading by Q127

I reread the node and completed Lean file after compilation. This is a second
pass by the same worker; the dispatcher explicitly prohibits starting other
agents, and the maintainer supplies the independent review. Each hypothesis and
the sole equivalence were checked against the mapping above: target smoothness,
both finite-type conjunctions, affineness, algebraic closedness, and IsMonHom are
all present; the source may be nonreduced. The base point object is Spec F with
identity structure map, so composition gives F-points over F rather than arbitrary
scheme morphisms. Faithful flatness uses the contravariant appTop map, not f on
topological points. No mismatch or correction was found. No definition data or
additional postponed theorem was introduced.
