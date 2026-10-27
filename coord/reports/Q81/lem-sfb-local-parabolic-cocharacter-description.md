## Worker report

The module states `AlgebraicGeometry.exists_localParabolic_cocharacter`, with one
postponed proof. Three real canonical maps give the universal Laurent coordinate,
the punctured-line inclusion, and the projection to the test algebra spectrum.
There are no new mathematical notions, new nodes, or dependency replacements.

Hypotheses and clauses, read against the complete node:

- A nonzero commutative Noetherian local ring: `(A : Type u) [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A]`. `IsLocalRing A` includes nontriviality, so the nonzero hypothesis is retained
  without an overlapping instance binder. The base is `Spec (.of A)`.
- Group schemes over that base: `G H T : Grp (Over (Spec (.of A)))`. Mathlib's
  `GrpObj`, bundled by `Grp`, supplies the actual multiplication, identity,
  inverse and all diagrams; the recorded group-scheme definition explicitly
  directs this encoding and works over any base.
- G smooth, affine and finitely presented: `[Smooth G.X.hom]
  [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]`. An affine
  morphism is quasi-compact and separated, so locally finite presentation here
  is equivalent to finite presentation; no finiteness clause was omitted.
- Closed subgroup chain T ⊆ H ⊆ G: group homomorphisms `j : T ⟶ H`, `i : H ⟶ G`
  with `IsClosedImmersion` on their underlying scheme maps. Bundled group maps
  already preserve the group law; no field-only subgroup predicate is applied
  to A. Smooth H is `[Smooth H.X.hom]`.
- Every geometric fibre connected and reductive: `hred` quantifies over every
  algebraically closed field Ω and map `A →+* Ω`, pulling back with the canonical
  `Over.pullback ... |>.mapGrp`. It uses `ReductiveTorusCentralizer.IsReductive`:
  smooth affine finite type, geometric connectedness, and triviality of every
  smooth connected normal unipotent closed subgroup over the algebraic closure.
  Its unipotence is the recorded faithful-matrix geometric-point condition.
  The smoothness and finite-type clauses are already implied by the structural
  assumptions on G and base change; they add no extra restriction.
- Parabolic geometric H fibres: `hpar` includes their connectedness and a group
  homomorphism `b : B ⟶ H_Ω` whose composite into G_Ω is `IsBorelGroupScheme`.
  This is exactly containing a maximal smooth connected solvable closed subgroup.
  The predicate uses the scheme-theoretic derived series. A Borel inclusion into
  G factoring through the closed H is closed into H as well. Smoothness of H_Ω
  follows from the stated smoothness of H, not an omitted hypothesis.
- Specified split torus of rank r ≥ 0: `(r : ℕ)` and
  `(e : T ≅ RingGroupSchemes.splitTorus A r)`. Its Laurent Hopf construction and
  finite products have real data; zero rank is the trivial group.
- Geometrically maximal torus fibres: `hmax` applies the existing
  `ReductiveTorusCentralizer.IsMaximalTorus` to the pullback of `j ≫ i`.
- There is a group homomorphism G_m,A → T: `∃ lam :
  RingGroupSchemes.multiplicative A ⟶ T`, a morphism of bundled group schemes.
- Every commutative A-algebra B: `∀ (B : Type u) [CommRing B] [Algebra A B]`,
  in the same object universe as the schemes, with no reducedness, nonzero or
  finite-type condition on B.
- H(B) inside G(B): existence of `h` with `h ≫ i.hom.hom = g`, equivalent to
  membership in the image subgroup because i is a closed immersion.
- The orbit extends to Spec B[t]: existence of `a` from
  `(algSpec (.of A)).obj (op (CommAlgCat.of A (Polynomial B)))` to G.X.
  Its restriction along `localParabolicPuncture A B` equals the product
  `(z ≫ lam ≫ j ≫ i) * (projection ≫ g) * (z ≫ lam ≫ j ≫ i)⁻¹`, where
  `z = localParabolicLaurentPoint A B`. Thus this is the scheme-valued orbit
  on Spec B[t,t⁻¹], not equality merely on geometric points. By the pullback
  universal property an A-map from this B-scheme to G is exactly a B-map to G_B.
  Quantifying over every B gives equality of the subgroup functors and, since all
  maps are canonical restrictions, retains their naturality.

Dependencies used (modules and declarations):

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (recorded dependency).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`, group
  homomorphisms and group structure on maps into group objects (through the
  public imports); these are the recorded def-sc-group-scheme declarations.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing`:
  `RingGroupSchemes.multiplicative`, `RingGroupSchemes.splitTorus`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsReductive`, `.IsMaximalTorus`.
- `Sheaf.AlgebraicGeometry.GroupScheme.Borel`: `IsBorelGroupScheme`.

The last three landed definition nodes are added to stmt_deps to cite the actual
interfaces used. No statement, proof or proof-dependency change is made.

Proof imports include the two recorded theorem modules HomogeneousQuotient and
BorelQuotientProperGeometry, plus the Mathlib matches
`UniversallyClosed.of_comp_surjective`, `IsLocalRing.map_mkQ_eq_top`, and
`Algebra.FiniteType.isNoetherianRing` through their owning modules. The remaining
seven group-theoretic/fibrewise proof nodes have no current lean or mathlib_match
record, so there is no recorded module to import. They are not statement
prerequisites; the docstring retains all six proof steps and their dependencies.

Source read: Conrad's primary author PDF,
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Proposition 5.2.3 and
proof on printed pp.152--153; Section 4.1 and Definition 5.2.1. Also read the latest
blueprint unit sk-thm-sf-ctf-stability. The node is a supporting local-base lemma,
not the unit statement. No source-based correction was needed.

Edge cases checked before and after writing: H=G is obtained from the zero
cocharacter and constant orbit; torus groups and empty root systems have the
same behaviour. With r=0, geometric maximality forces the reductive fibres to
be trivial, and the zero cocharacter remains valid. No positivity of r, root
nonemptiness, characteristic assumption, henselianity, or reducedness of A is
introduced. For upper triangular matrices in GL₂, the cocharacter diag(t,1)
makes the lower-left entry t⁻¹c; polynomial extendability forces c=0 also in a
nonreduced B, agreeing with the subgroup scheme. The zero test ring B is allowed.
The orbit uses actual Laurent maps, so no density-of-points inference is involved.

Searches:

- msearch leansearch: "Parabolic subgroup scheme over a local base is defined by
  extension of conjugation along a cocharacter" — 8 hits, matrix parabolic
  conjugation and ConjAct group structures, no group-scheme theorem.
- msearch leanfinder: "Over a local ring every parabolic containing a split maximal
  torus is the limit subgroup of a cocharacter" — 8 hits, abstract Lie/root-space
  results, no matching relative statement.
- msearch loogle: `"cocharacter"` — 0 hits.
- msearch grep: `cocharacter|parabolic`, Mathlib AlgebraicGeometry — 0 hits.
- rg on project WeilConjectures: `cocharacter|parabolic`, and the literal item id:
  no matching theorem. rg on Sheaf found field tori, Borel, reductive terminology,
  the recently landed ring split-torus construction and DVR Cartan decomposition;
  the latter was read as a consumer example, not used in place of this result.
- Read full signatures and docstrings of the six original statement dependency
  declarations, including `GrpObj` and the spectrum, and the three added landed
  interfaces. The obsolete CompactObject example is withdrawn; its node redirects
  to the upstream module, so no withdrawn definition was copied.

No STATEMENT-DISPUTED or node fault remains.

## Second reading by Q81

A separate reading pass by the dispatched worker matched every binder and clause
as detailed above. It checked the direction of conjugation and inverse, coefficient
extension A→B, the puncture B[t]→B[t,t⁻¹], and the fact that the two sides live in
one Hom group. The generic coordinate sends z to t and does not pick an arbitrary
unit. The rank-zero product and the Borel-containing convention were checked in
the definitions, rather than inferred from their names. No mathematical mismatch
was found. The first compile caught use of the reserved token λ as a binder; it
was renamed `lam`. Independent review is left to the maintainer, as the dispatcher
explicitly prohibits starting other agents.

Compiler follow-up: removed the redundant Nontrivial instance binder, since
IsLocalRing includes it. This resolves the overlapping-instance warning without
changing the nonzero-ring assumption.
