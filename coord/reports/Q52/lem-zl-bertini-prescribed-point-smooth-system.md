## Worker report

The module Sheaf.AlgebraicGeometry.BertiniPrescribedPointSmoothSystem states
AlgebraicGeometry.exists_eventual_prescribedPoint_smoothSystem, with `sorry` as its only
postponed proof. Seven accompanying definitions/abbreviations construct the actual projective
twist, coefficient combination, vanishing predicate, first-order target and value, restricted
section family, and zero ideal. No independent mathematical notion is assumed or replaced by
an arbitrary map. The module compiled cleanly through scompile.py, both as a sandbox module
and under its actual library name (6.4 s and 8.3 s respectively).

Source read: the whole blueprint main-20261015 proof of
lem-zl-bertini-finite-cover-curve, especially paragraph 2 and its displayed jet map;
varieties.tex lemma-generate-over-complement (0FD5) and lemma-bertini (0FD6).
The theorem docstring includes all twelve proof steps from the node, with their dependencies.

Hypotheses and objects, clause by clause:

- An algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The affine k-scheme is `X : Scheme.{u}`, `[X.Over (Spec (.of k))]`, `[IsAffine X]`.
  Connectedness is Mathlib `ConnectedSpace X`, including nonemptiness.
- Smoothness is `[Smooth (X ↘ Spec (.of k))]`. Finite type is its locally finite type
  and quasi-compact factors. No characteristic hypothesis is imposed.
- `d : ℕ`, `hd : 2 ≤ d`, `hdim : X.IsPureDimension d` retain the exact dimension bound
  and the recorded notion of purity, including its underlying topological definition.
- `S : Finset X`, `hS : S.Nonempty`, and `hclosed : ∀ x ∈ S, IsClosed {x}` give the
  finite nonempty set of rational points: for a finite-type scheme over an algebraically
  closed field, closed points and k-rational points correspond bijectively. The field
  structure morphism fixes the rational-point structure uniquely. There are no repeated
  points. Vanishing is tested in each residue fibre, so the subscheme is reduced, with
  no thickening silently introduced.
- The fixed closed embedding in affine N-space and its projective closure are encoded by
  `N`, the reduced scheme `Y`, the closed immersion `c : Y ⟶ ℙ(ULift (Fin (N+1)); Spec k)`,
  and the open immersion `j : X ⟶ Y`. `hdense : DenseRange j` and `hchart` say exactly that
  X is the dense intersection with D_+(T_0). This intersection is closed in that affine
  N-space because c is a closed immersion. Reducedness and density make Y precisely the
  reduced projective closure of this embedding, rather than an arbitrary compactification
  with boundary components or nilpotents. `hover` asserts that the embedding is over k.
  Conversely the source's fixed embedding and closure supply exactly these data.
- `prescribedPointTwist c n` is the canonical tensor pullback of projective `O(n)`, with
  no arbitrary line bundle or ample replacement. Naturals index the eventual integers:
  a bound can always be increased to be nonnegative, losing no eventual integer case.

Conclusions, clause by clause:

- `∃ n₀, ∀ n, n₀ ≤ n → ...` is the uniform eventual quantifier. The open `U` satisfies
  `∀ x, x ∈ U ↔ x ∉ S`, so it is exactly X minus the prescribed points.
- For each n, `I : Type u`, `Fintype I`, and `s : I → Γ(prescribedPointTwist c n, ⊤)`
  give a finite basis of V_n. The first conjunct says that a section v vanishes after
  restriction to S if and only if there is a unique coefficient tuple `a : I → k` with
  `prescribedPointCombination ... s a = v`. The combination uses scalars through the
  actual structure morphism of Y, not a separately supplied scalar action.
  This is a coordinate presentation of exactly the kernel in the node and includes its
  finite dimensionality. In particular applying the unique-representation condition to
  zero forces injectivity of the coefficient map, and all its values vanish on S.
- Vanishing in `prescribedPointVanishes` means the restricted germ belongs to m_s L_s.
  This is precisely zero in the fibre L(s). For the reduced finite S these simultaneous
  conditions are equivalent to zero restriction in Γ(S,L|_S), the stated kernel.
- The existential `ht : Epi (...freeHomEquiv.symm ...)` is the recorded generating-sections
  definition applied to the restricted basis. `prescribedPointRestrictedFamily` uses
  tensorSectionsUnit and the existing compatible-section conversion. The following
  `IsImmersion (@ProjectiveSpace.homOfGeneratingSections ... ht)` is exactly the morphism
  associated with those same sections on X minus S.
- `Function.Surjective (fun a ↦ fun x : S ↦ prescribedPointJet ... x.val ...)` is simultaneous
  first-order surjectivity. A product over the finite subtype S is the finite direct sum.
  `PrescribedPointJet M x` is `(m_x/m_x²) ⊗[O_x] M_x`. Since m_x annihilates its cotangent
  quotient, this is canonically `(m_x/m_x²) ⊗[κ(x)] (M_x ⊗[O_x] κ(x))`; since x is rational,
  it is the tensor over k in the node. The map takes the actual germ of the actual
  restricted coefficient section. In a stalk frame it is `[a] ⊗ e`, where the germ is a e.
  Changing e by a unit multiplies the first factor by the inverse unit, so this is the
  canonical first-order value, independent of the selected frame. The branch returning
  zero for a section not vanishing at x is never reached on the kernel used here.
- `O : (Spec (CommRingCat.of (MvPolynomial I k))).Opens`, with `O.Nonempty` as a set,
  is the nonempty Zariski open in affine coefficient space A(V_n). The condition
  `Set.range (bertiniCoefficientPoint (k := k) a) ⊆ O` means the k-point a lies in O.
  This uses the published actual evaluation morphism, not an arbitrary parameter map.
- `prescribedPointMember ... s a` is the zero ideal of the actual tensor-pulled-back
  combination on X. Its `.subscheme` and `.subschemeι` are the recorded zero scheme and
  its closed immersion, so closedness is supplied by that construction itself.
- `Smooth (H.subschemeι ≫ (X ↘ Spec k))`, `IsAffine H.subscheme`, and
  `H.subscheme.IsPureDimension (d - 1)` state smoothness, affineness, and pure dimension.
- `∀ x ∈ S, x ∈ H.support` states containment of S; because S is reduced, vanishing of
  the defining section also gives its scheme-theoretic containment. The final conjunct
  says `prescribedPointJet ... x ... ≠ 0` at every prescribed point.

Dependency declarations read and used:

- The two scheme-convention nodes explicitly collect Mathlib notions rather than defining
  declarations of their own. Here Scheme, Scheme.Over, IsAffine, Smooth, IsOpenImmersion,
  IsClosedImmersion, LocallyOfFiniteType, and QuasiCompact retain those meanings.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  AlgebraicGeometry.Scheme.Modules.IsInvertible (local rank-one trivializations).
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators:
  SheafOfModules.GeneratingSections, equivalently the Epi freeHomEquiv condition.
- Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections:
  AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections, including its full finite-index
  signature, selected universal pair, and pullback projections.
- WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus:
  AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus, whose ideal is the dual section image.
- WeilConjectures.AlgebraicGeometry.BaseChangeConventions:
  Scheme.Modules.moduleBaseChange and its use of tensorPullback for module pullback.
- Mathlib.Topology.Connected.Basic: ConnectedSpace, including nonemptiness.
- Sheaf.AlgebraicGeometry.PureDimension: Scheme.IsPureDimension, quantifying over all
  irreducible components, not just a maximum dimension.
- Three already-landed dependencies are added to stmt_deps under brief-stage2 §5:
  def-pc-projective-space-twist (ProjectiveSpace.twist),
  lem-weil-pbc-invertible-stalk-linear-equiv (invertible_stalk_linearEquiv), and
  lem-weil-pbc-invertible-pullback-tensor (invertible_pullback_tensor).
  Their recorded modules and full signatures were read. The jet frame is obtained from
  the proved rank-one stalk theorem, not from a new sorried existence assertion.
  Pullback invertibility proofs are passed explicitly from the recorded theorem.
- The existing BertiniSmoothMember module supplies bertiniCoefficientPoint and
  bertiniSectionFamily. All recorded proof-dependency modules that have modules are
  imported; none introduces an import cycle. Mathlib proof leaves have explicit private imports of
  their recorded source modules; no proof dependency is restated here.

Edge cases checked: d=2 yields smooth curves of pure dimension one. Any finite nonempty
number of distinct prescribed points is permitted. Empty S is intentionally excluded by
hS as the source requires; empty X is excluded both by ConnectedSpace and S.Nonempty.
The finite coordinate type is not forced nonempty: the clauses themselves rule out a
zero-dimensional V_n when nonzero jets are required. The singular projective boundary is
allowed; only X is smooth. The zero scheme may be disconnected, since the node asserts
purity and smoothness but not connectedness. Characteristic p is unrestricted. N=0 and
other impossible embeddings are not artificially removed by an extra dimension bound.
The jet definition is valid for arbitrary stalk frames and arbitrary section values; its
nonvanishing branch is unused for V_n. No universe equality excludes any field or scheme
in the stated common geometric universe; finite basis indices use the same universe.

Searches actually run:

- msearch.py leanfinder: "High degree sections vanishing at finitely many prescribed points
  separate first order jets and have smooth zero scheme". Eight results: projective
  separation, local smooth charts, polynomial functions separating points, and section
  localization; no statement of this theorem or canonical prescribed-point jet map.
- msearch.py loogle: "IsLocalRing.CotangentSpace, Ideal.Cotangent, Submodule.mapQ".
  Zero hits for the combined query. Direct source reading then located Ideal.toCotangent
  and IsLocalRing.CotangentSpace in Mathlib/RingTheory/Ideal/Cotangent.lean, which are used.
- msearch.py grep: "firstOrder|first.order|jet|Jet" in AlgebraicGeometry. Zero Mathlib hits.
- msearch.py leansearch: "High powers of ample invertible sheaves separate first order jets
  at finite closed points". Eight hits on powers in Proj, localization of sections,
  sheaf generators, and stalk maps; none is this statement.
- rg in lean/WeilConjectures and lean/Sheaf for the item id: no declaration attached to it.
  Broader first-order/jet/prescribed-point/vanishingSections searches found BertiniSections
  (the proof input), BertiniSingularFirstOrderModel (a different singular-fibre assertion),
  and the published smooth-member helpers; all were inspected rather than duplicated.
  Name searches for prescribedPoint, prescribedJet, prescribedTwist and
  prescribedCombination in Mathlib, WeilConjectures and Sheaf returned no collision.

No statement correction, disputed claim, new node, or dependency-interface replacement.

## Second reading by Q52

A fresh worker reread matched the written theorem against the node and the source after
compilation. The dispatcher explicitly forbids starting other agents, so this section is a
second pass by the submitting worker; the maintainer's independent review remains separate.
The check specifically revisited the equivalence of rational and closed points over the
algebraically closed base; the reduced dense affine-chart characterization of the fixed
projective closure; the unique-coefficient kernel condition (including the zero section);
the balanced local-ring tensor model of the displayed jet target; finite product versus
finite direct sum; and scheme-theoretic containment of the reduced S. The resulting
statement retains generation, immersion, simultaneous surjectivity, and every smooth-member
clause without replacing them by hypotheses. Compiler feedback caused public-import,
explicit-invertibility, coordinate-type, and scope fixes; no mathematical hypothesis or
conclusion was changed. All definitions contain actual data; the only sorry is the main
theorem, with the node's complete proof in its docstring.
