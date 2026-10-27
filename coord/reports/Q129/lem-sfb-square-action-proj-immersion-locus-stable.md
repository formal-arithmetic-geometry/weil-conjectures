## Worker report

The module `Sheaf.AlgebraicGeometry.SquareActionProjImmersionLocusStable` states
`AlgebraicGeometry.Scheme.Modules.squareAction_proj_immersion_locus_stable` with its
whole proof `sorry`. Its only other declaration, `squareActionTranslation`, is a
concrete construction by the existing Cartesian pairing, projections, and action.
No new DAG notion is introduced: this is the translation already specified in the
item itself. No node fields other than `lean` change. No statement fault or
STATEMENT-DISPUTED flag was found.

Source read: Guo, *Divisors on coherent schemes and homogeneous spaces*, March 31,
2026 version, https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf,
section 5.6 (Picard-admissibility modulo base modules), section 6.1 (canonical Proj
map and setup), and Proposition 6.2(iii), printed pp.14--15. The current blueprint
unit `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was read as well; this auxiliary result is not that unit's own statement. On an
affine base the source's relative ampleness becomes absolute ampleness, as in the
node's explicit specialization. The point-image and quasi-compact-open clauses
are precisely those of Proposition 6.2(iii).

Hypotheses and clauses, individually:

- Affine scheme S: `(S : Scheme.{u}) [IsAffine S]`, with unrestricted universe u.
- H and X over S: `(H X : Over S)`. Their structural maps are `H.hom`, `X.hom`.
- Group scheme structure and all its identities: `[GrpObj H]`. Mathlib's group
  object has multiplication, unit, inverse and their morphism identities, not just
  an abstract action on rational points.
- H smooth: `[Smooth H.hom]`. H separated: `[IsSeparated H.hom]`, whose definition
  is the closed-immersion diagonal. H finite presentation:
  `[LocallyOfFinitePresentation H.hom] [QuasiCompact H.hom]`, together with the
  already assumed separatedness, which implies quasi-separatedness.
- Connected fibres: `hconnected : ∀ s : S, ConnectedSpace (H.hom.fiber s)`.
  The fibre is `pullback H.hom (S.fromSpecResidueField s)`; ConnectedSpace includes
  nonemptiness, so the empty fibre is not inadvertently called connected.
- X separated and of finite presentation: `[IsSeparated X.hom]`,
  `[LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom]`.
- The S-action and its identity/associativity identities: `[ModObj H X]`, with map
  `(γ[H, X]).left : (H ⊗ X).left ⟶ X.left`. The existing Cartesian monoidal
  structure on Over S identifies the product with the scheme fibre product.
- Invertible module: `(M : X.left.Modules) [M.IsInvertible]`, the recorded
  scheme-module notion, not a new sheaf class.
- Every S-test scheme B and both sections: `∀ (B : Over S) (g h : B ⟶ H)`.
  All schemes, including X and H and their universal parameter schemes, have
  the same arbitrary scheme universe u; there is no independent smaller test
  universe and no restriction to affine, smooth, or field-valued tests here.
- X_B is represented by `(B ⊗ X).left`, i.e. B ×_S X, using the canonical symmetry
  of X ×_S B. The projection to X is `(snd B X).left`, q_B is `(fst B X).left`.
  M_B is exactly `(tensorPullback (snd B X).left).obj M`.
- Translation τ_g is `squareActionTranslation H X B g`; its body pairs b with
  the action of g(b) on x. Multiplication `g * h` uses H's group-scheme law.
- The square condition `hsquare` is `∃ N : B.left.Modules, N.IsInvertible ∧
  Nonempty (...)`: the isomorphism has left side τ_gh^* M_B ⊗ M_B and right side
  `(τ_g^* M_B ⊗ τ_h^* M_B) ⊗ q_B^* N`, exactly with the indicated parentheses.
  Every pullback is the recorded `tensorPullback`; every tensor is the existing
  module-sheaf monoidal tensor. Nonempty asserts existence of an isomorphism;
  it supplies neither coherence nor a chosen family.
- The positive-degree nonvanishing cover is `hcover`, exactly the hypothesis of
  `exists_sectionRing_proj_morphism`. An element `s : sectionRingGrade M d`
  is a homogeneous degree-d section embedded in the direct-sum section ring;
  `s.val d` is its actual section. This ranges over all such sections.
- A and P are the existing `InvertibleSectionRing M` with `sectionRingGrade M`
  and `Proj (sectionRingGrade M)`, not replacement graded algebras.
- Canonical r: `(r : X.left ⟶ Proj (sectionRingGrade M))` and `hr`, copied from
  the exact conclusion of `exists_sectionRing_proj_morphism`. This includes
  BOTH inverse images of D₊(s) and the localized fraction formula, so r is not
  an arbitrary map with a set-theoretic characterization only. The fraction
  formula is its division-free version: r^*(ξ/s^n) times s^n equals ξ on X_s.
- P₀: an open `P₀` and `hP₀ : P₀ = sSup {V | IsOpenImmersion (r ∣_ V)}`.
  `r ∣_ V` is the existing morphism from the entire inverse image to V.
  Supremum of opens is exactly their union, including the empty collection.
- W: written directly as `r ⁻¹ᵁ P₀`; no statement-level let or opaque choice.
- Image of H ×_S W: `(γ[H, X]).left '' ((snd H X).left ⁻¹' W)`.
  The inverse image of the open W under the second projection is the open
  subscheme H ×_S W. Restricting to it does not change its action-image set.
  Equality with W is the first conjunct; all underlying fibre-product points
  are included, rather than only residue-field rational orbit points.
- Every quasi-compact open in W: `∀ (T : X.left.Opens), T ≤ r ⁻¹ᵁ P₀ →
  CompactSpace T.toScheme → ...`. Opens of W are equivalently opens of X
  contained in W; compactness is their intrinsic topological compactness.
- Absolute ampleness: `@IsAmple T.toScheme (M.restrict T.ι) (...)`, the existing
  absolute definition. The explicit invertibility witness transports the
  existing invertible pullback along `restrictFunctorIsoPullback`; it only
  supplies proof data needed to type IsAmple, and is not an extra hypothesis
  or postponed theorem. `M.restrict T.ι` is the actual restriction sheaf.

Dependency declarations read and reused (including complete signatures/docstrings):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, Scheme.Hom;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, fst, snd;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`;
  `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`;
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` publicly retains
  `Scheme.Modules.tensorPullback` of `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` publicly retains
  the existing module-sheaf tensor. The scheme monoidal instance is the existing
  `Scheme.Modules` instance of `Modules.Invertible`; no new tensor is defined.
- `WeilConjectures.AlgebraicGeometry.Ample`: `nonvanishingLocus`, `IsAmple`;
  `WeilConjectures.AlgebraicGeometry.InvertibleSectionRing`: `InvertibleSectionRing`,
  `sectionRingGrade`; `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`: `Proj`.
- `WeilConjectures.AlgebraicGeometry.AmpleProjCanonicalMap`:
  `Scheme.Modules.exists_sectionRing_proj_morphism` (its exact chart conclusion is hr).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- Group/action interfaces: `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`,
  `Mathlib.CategoryTheory.Monoidal.Mod`: `GrpObj`, `ModObj`, γ, fst, snd, lift;
  Mathlib's Cartesian structure for `Over S` uses the chosen scheme pullback.

The stated proof dependencies' modules are plain imports, including proper/smooth
base change, smooth flatness, universally open flat-lfp maps, fpqc precoverage and
open-immersion descent, affine qcqs, canonical twist comparison, quasi-compact Proj
open ample twists, and ample isomorphism invariance. The genuine unstated proof
prerequisite `lem-sfb-square-action-proj-translation-extension` has no Lean record
or published module in the read clone and is therefore not imported. It is a
proof dependency only, so no statement construction is missing and no waiting or
duplicate theorem is needed. Stage 3 can import it when it is stated.

Searches actually run:

- msearch.py leanfinder: “The open immersion locus of the canonical section ring
  Proj map is stable under a group action satisfying the theorem of the square”.
  Eight results: Proj chart open immersions, pullback charts, and section-induced
  Proj maps/restrictions. Their types are not this action/ampleness theorem.
- msearch.py loogle: `"Proj", "IsOpenImmersion"`. One result:
  `AlgebraicGeometry.Proj.instIsOpenImmersionAwayι`, only an affine Proj chart.
- msearch.py grep: `squareCondition|openImmersionLocus|Picard.admiss` in
  Mathlib/AlgebraicGeometry. Zero hits.
- msearch.py leansearch: “A square-condition invertible sheaf has group-stable
  open immersion locus of its canonical morphism to the Proj of its section ring”.
  Eight results: Proj.fromOfGlobalSections, chart open immersions, quasi-affine
  affinization, and open-immersion section maps. No exact match.
- rg over lean/WeilConjectures and lean/Sheaf for SquareCondition, squareCondition,
  square_condition, squareAction, targetOpenImmersion, immersionLocus: unrelated
  categorical tensor comparison squares only. Search for the item's exact id
  in lean/WeilConjectures: no hits. Search for both proposed full name components
  in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json: no hits.

Edge cases checked before writing: X empty, S empty, T empty, W empty, P₀ empty,
the trivial group, a trivial line bundle, finite presentation over a non-Noetherian
affine base, arbitrary characteristic, and non-rational points of a fibre product.
No Nonempty X/S/T, Noetherian hypothesis, characteristic restriction, commutativity
of H, linearization, coherent choices, or ampleness of M on all X is imposed.
Positive degrees are required only where the source requires them; the degree-zero
part remains in the section ring. The formula handles n = 0 and empty chart opens.

Validation: the prescribed scompile.py compiled this file in sandbox and library
modes on the published live server, in 3.9 s and 2.9 s respectively, with no errors
or warnings. The only postponed result is the single named main theorem.

## Second reading by Q129

A second direct reading of the node and the completed module checked the square
condition's three pullbacks and tensor factors, the base-change product order,
the connected-fibre nonemptiness, and both canonical-map chart clauses. This is
an in-thread second pass; no other agent was started, as the dispatch brief forbids
that. The maintainer's independent review remains the independent reading.

The potentially ambiguous point-image expression was checked explicitly: the
set `(snd H X).left ⁻¹' W` is precisely the underlying open fibre product H × W,
so its action image is the requested image of that subscheme. It does not replace
scheme-fibre-product points by pairs of rational points. The final quantifier
ranges over opens of X contained in W, which is equivalent to opens of W, and
uses actual restriction plus absolute IsAmple. Finite presentation is lfp + qc
with separatedness supplying qs, without adding a stronger finite-type condition.
No mismatch was found and no statement correction was made.
