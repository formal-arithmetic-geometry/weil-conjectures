## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.DoubleFlagInvariantBoundary` states
`AlgebraicGeometry.exists_double_flag_invariant_boundary`, with one `sorry` proof.
The four supporting definitions contain real data: the external square is the tensor
of the two ordinary module pullbacks, its frame is the composite of canonical
pullback-composition and monoidal isomorphisms, `coefficient` applies this frame to
the pulled-back section, and `rightInvariants` is `AlgHom.equalizer` of right
translation and first projection. They belong to this node's specified constructions,
not new independent notions or arbitrary choices.

The natural-language statement, statement dependencies and proof are unchanged.
No dependency interfaces were replaced. All variables and the single universe `u`
are explicit, with `autoImplicit false`.

Hypotheses and clause matching:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The group schemes are `S T B : Grp (Over (Spec (.of F)))`, using the recorded
  internal group-object definition. `hS : IsSemisimpleGroupScheme S.X` uses the
  recorded smooth connected affine finite-type semisimplicity predicate.
- Simply connected is exactly `hsc` from `exists_rho_section_modules`: every
  surjective central finite-kernel map from a semisimple group is an isomorphism.
  Centrality is tested on every commutative F-algebra, as in that dependency.
- The split maximal torus, Borel, and inclusions are `iT`, `iB`, `j` and
  `hpair : IsRhoBorelPair iT iB j`. This predicate includes splitness, maximality,
  the Borel condition and the commuting inclusion triangle.
- The positive roots and half-sum character use exactly the recorded rho interface:
  `a` and `ha` specify conjugation; `Φ`, `hΦ`, `hroots` enumerate each nontrivial
  character weight of Lie(B) once; `hρ` is twice rho equal to the sum of positive
  roots, written multiplicatively, without division in F. `hρB` restricts the
  extension to rho, and `hρU` says it is trivial on the unipotent radical, using
  the dependency's characterization on every connected normal unipotent subgroup.
- The negative character is the actual character `χ` with
  `hχ : χ.hom.hom = ρB.hom.hom⁻¹`. It is not an unrelated weight.
- `Q`, `π`, `hQ`, `hQft`, `hQqc`, `hπflat`, `hπsurj`, `hπinv`, and `hπtorsor`
  are the flag quotient and precisely its proper finite-type right-B-torsor
  presentation supplied by `reductive_borel_pair_structure`.
- `P : AssociatedCharacterLineBundle.Presentation S B iB Q π χ` supplies the
  homogeneous sheaf, its canonical frame on S, and its natural left action;
  `hL` is the invertibility supplied by `exists_homogeneousLineBundle_sections`.
- `X` is the categorical product `Q ⊗ Q` in `Over (Spec F)`, hence the scheme
  fibre product over F. `DoubleFlag.externalSquare Q P.L` is exactly
  `pr₁^* L ⊗ pr₂^* L`, with the existing ordinary pullback and sheaf tensor product.
- The first three conclusions are `IsIntegral (Q ⊗ Q).left`,
  `QuasiCompact (Q ⊗ Q).hom` and `IsSeparated (Q ⊗ Q).hom`. Mathlib's
  `IsIntegral` includes nonemptiness and is equivalent to irreducible and reduced.
- `n₀ : RankOneRoots.normalizer iT` is a genuine normalizing F-point, with
  normalization tested after scalar extension by that existing definition.
- The subgroup intersection is equality of point subfunctors on every
  `Z : Over (Spec F)`, not just F-points. The left set explicitly requires
  membership in B and in n₀Bn₀⁻¹; the right set is `pointImage iT Z`.
- `d : Γ(DoubleFlag.externalSquare Q P.L, ⊤)` and `d ≠ 0` are the required
  nonzero global section. Invariance is the identity of `coefficient` at
  `(s*g,s*h)` and `(g,h)` for every test scheme Z and all s,g,h. The frame is
  induced from the two specified homogeneous trivializations, not an existential
  linearization. Its coordinate z is unchanged by left multiplication by the
  `Presentation.totalAction_coordinate` identity. Thus this is precisely the
  induced diagonal linearization's invariance, as a rational coaction identity.
  Pullback to S×S is faithfully flat, so these equalities detect the section
  equality on the double flag and after base change.
- `U` is an open of X whose underlying set equals
  `Scheme.Modules.nonvanishingLocus (DoubleFlag.externalSquare Q P.L) d`.
  That existing predicate is a nonzero fibre value; for an invertible module,
  Nakayama gives equivalently that the germ generates its rank-one stalk.
- `Dense (U : Set X)` is the claimed density. The orbit map is `q`, with
  `q.left ≫ U.ι` required to equal the actual morphism
  `lift π ((𝟙 S.X * (toUnit S.X ≫ n₀.val)) ≫ π)`, giving exactly
  g ↦ (gB,gn₀B). It has image U because `Surjective q.left` is asserted.
- `Flat q.left ∧ Surjective q.left` is faithful flatness with the specified meaning.
  The right-action invariance equation and `IsPullback fst rightAction q q`
  express the canonical right T-action and torsor kernel-pair isomorphism.
- `aU : ModObj S.X U` is the induced action, pinned by
  `lift s (g ≫ q) ≫ aU.smul = (s*g) ≫ q` on every test scheme.
- `e : Coordinate U ≃ₐ[F] DoubleFlag.rightInvariants iT` is an F-algebra
  isomorphism, and `(e r).val = ((algΓ (.of F)).map q).unop.hom r`
  forces it to be q^*, rather than an unspecified algebra isomorphism.
  The equalizer uses the two canonical maps on the entire S×T, hence is exactly
  f(gt)=f(g) after every commutative F-algebra extension. The universe u of test
  algebras matches the group schemes, as in the dependency interface.
- The last formula compares the value of e(r) on s⁻¹g with the value of r on
  s⁻¹ acting on q(g). It is equivariance for left translation with exactly the
  convention `(s f)(g)=f(s⁻¹g)`, universally in the test scheme.
- The trivial-group clause imposes no separate hypothesis: the theorem includes
  the empty positive-root list, torus rank zero, and the trivial group. In this
  specialization rho and its extension are trivial, L and its external square
  are trivial, Q=X=U=Spec F up to the canonical scheme isomorphisms, d is a
  nonzero constant, and the orbit map and algebra comparison are identities.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` (the algebraic-closure node explicitly records this predicate).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`; schemes and scheme
  morphisms are `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.RhoSectionModules`: `IsRhoBorelPair`,
  `exists_rho_section_modules`; its public imported `RhoSectionModuleData`
  provides the actual `RhoSection.Coordinate` and semi-invariant conventions.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `reductive_borel_pair_structure`, `semisimpleGroupScheme_isReductive`.
- `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections`:
  `exists_homogeneousLineBundle_sections`; its public imported
  `AssociatedCharacterLineBundle` provides `Presentation`, `trivializationAt`
  and `pullTopSection`, read in full with their defining data and docstrings.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, the ordinary sheaf tensor product.
- Morphism-convention node has no independent declaration. The corresponding
  Mathlib classes `QuasiCompact`, `Flat`, `Surjective`, `IsSeparated` and
  `IsProper` are used through these public imports.
- `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`: `normalizer`
  and `pointImage`, used rather than an abstract normalizer or Weyl group.
- Canonical structural APIs: `Scheme.Modules.pullback`, `pullbackComp`,
  `pullbackCongr`, `Functor.Monoidal.μIso`, the unit unitor, `AlgHom.equalizer`,
  and `Scheme.Modules.nonvanishingLocus`. The latter is defined in the existing
  `WeilConjectures.AlgebraicGeometry.Ample` module.
- Proof-only imports are `BruhatLongestCellCharts.bruhat_longest_cell_charts`,
  `GeometricallyIrreducibleProduct.geometricallyIrreducible_pullback_over_field`,
  `RhoRegularWeylOrbit.rho_regular_weyl_orbit` (all in AlgebraicGeometry), and
  Mathlib's Proper module (proper base change and composition instances).
  The proof dependency `lem-sfb-induced-module-primitive-line` has no recorded
  module or declaration in the current DAG, so there is no import to add yet;
  its full natural-language role remains in the proof docstring. It is a proof
  dependency only and does not obstruct this statement.

Edge cases checked before and after drafting:

- Rank zero: Φ=[] is allowed; no nonempty root, torus or index hypothesis.
- SL₂: L=O(1), X=P¹×P¹, the determinant of the two column lifts is the section;
  its nonvanishing pairs are distinct lines and the stabilizer is T. The
  simultaneous-left coefficient identity and both right rho factors have the
  expected signs. Characteristic 2 is included: no division by 2 in F is used.
- Arbitrary characteristic: characters, not their Lie differentials, specify
  rho and its positive roots.
- Nonreduced test schemes: frame invariance and the subgroup intersection are
  quantified over every scheme; right invariance is equality of algebra maps,
  not an identity only on geometric points.
- Empty U cannot satisfy faithful flat surjectivity from S; d≠0 and integrality
  give the expected nonempty open. No empty-scheme case of the claimed geometry
  was silently admitted by a hollow hypothesis.
- The section's nonvanishing is fibre nonvanishing/generation, not merely a
  nonzero element of a stalk.

Searches (2026-10-24), before writing, with the prescribed msearch wrapper:

- LeanFinder, `invariant section opposite double flag orbit rho line bundle`:
  eight unrelated representation induction and topological vector-bundle hits;
  none gives this scheme statement.
- Loogle, `Scheme, IsOpenImmersion, IsPullback, IsInvariant`: no hit (unqualified
  Scheme is not recognized by the remote index). Read the local scheme, group,
  module, monoidal pullback and subalgebra signatures directly.
- LeanSearch, `An invariant rho section cuts out the dense opposite orbit in a
  product of flag varieties`: eight unrelated topological orbit/minimal-action
  or generic dominant-map facts; no double-flag section theorem.
- Mathlib grep, `opposite.*flag|double.flag|Bruhat`: only the Bruhat--Tits-tree
  comment in `Algebra/Module/Lattice.lean`; no match.
- msearch grep, `double.flag|invariant.*section|rho.*section` against the upstream
  root: zero hits.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `double.flag|opposite.*flag|invariant.*rho`, and grep for this node id in
  `lean/WeilConjectures`: no declaration for the requested statement.
- Direct rg for `externalSquare|externalTensor|rightInvariants|` the proposed
  theorem name across Mathlib/upstream/Sheaf found generic external tensor-section
  computations only. No definition of these particular constructions existed;
  the helpers compose the canonical existing pullback, tensor and equalizer APIs.

Source checked: the local Milne PDF, printed pp.450--451 (21.80, 21.83--21.86)
contains the Bruhat charts, diagonal double-flag orbit description and opposite
Borel intersection. Printed pp.479--480 (22.48--22.49) gives the homogeneous
section/semi-invariant convention and rho. The node is explicitly agent-formulated
from these, not a claimed quotation. Its eight proof steps are retained in the
Lean docstring. No statement correction or disputed mathematical assertion.

Validation: scompile.py compiled this file both as its sandbox module and as
`Sheaf.AlgebraicGeometry.GroupScheme.DoubleFlagInvariantBoundary` cleanly,
10.1 and 9.6 seconds respectively under the default 60-second limit. No raised
heartbeat limit, no unexpected warning, and no definitions containing sorry.

## Second reading by O2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
