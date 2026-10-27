## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.ClosedTranslationStabilizer`
states `AlgebraicGeometry.exists_closed_translation_stabilizer`. Its sole proof is
`sorry`; there are no new definitions, extra nodes, dependency modules, or statement
corrections. The repository node is unchanged except for its `lean` field.

Hypotheses and clauses, matched individually:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Abelian variety over k: `(A : Over (Spec (.of k))) [GrpObj A]
  [IsAbelianVariety A]`. No characteristic, dimension, or projectivity assumption
  is imposed. The multiplication notation on morphisms is the existing group
  object's multiplication; it denotes addition on A.
- Closed subscheme Z of A: `Z : Over (Spec (.of k))`, `z : Z ⟶ A`, and
  `[IsClosedImmersion z.left]`. Its actual scheme structure is retained in
  `z.left.ker`, not replaced by its underlying closed set.
- Translation for any k-scheme T and a in A(T): `T : Over (Spec (.of k))`,
  `a : T ⟶ A`, and `(fst A T * (snd A T ≫ a)).left`. This morphism from
  A times T to A is `(x,t) ↦ x+a(t)`. Its pullback of the Z ideal is the
  inverse image of Z_T under translation. Translation is invertible, so equality
  with the projection pullback is equivalent to `t_a(Z_T)=Z_T`.
- Representing closed subgroup: the existential H, its `GrpObj H`, the inclusion
  `i : H ⟶ A`, and `IsClosedSubgroupScheme i`. The first universal clause says
  `(∃! b : T ⟶ H, b ≫ i = a)` if and only if the two pulled-back ideals agree.
  Equality is equality in `IdealSheafData`, hence equality of closed subschemes,
  including nilpotents. Composition with i gives the representing correspondence;
  it is natural because factorization through a fixed inclusion commutes with
  precomposition. No arbitrary equivalence or unrelated map is postulated.
- Arbitrary base change: the second universal clause quantifies over S, T, s and a.
  A point of A_S is the pair `(a,s)`; its unique lift to H_S is expressed by
  `b : T ⟶ H ⊗ S`, `b ≫ fst H S ≫ i = a`, and `b ≫ snd H S = s`.
  The same ideal equality is tested on A_T. Thus H_S represents precisely the
  stabilizer of Z_S, for every S, including nonreduced and nonaffine bases.
- Effective Cartier divisor F: `F : A.left.IdealSheafData` and `F.IsInvertible`.
  This is the existing locally regular-principal ideal predicate, i.e. locally
  one non-zero-divisor; it is not just invertibility of an arbitrary module.
- Z equals the reduced support: `z.left.ker = F.radical`. Taking the radical ideal
  gives exactly the reduced closed subscheme on the support, including F empty.
- C = (H_red)^0: `GrpObj.reduced H` is the existing reduction. The existential open
  U has underlying set `(GrpObj.reducedι H).left ⁻¹'
  connectedComponent (GrpObj.onePoint H)`. Reduction is a homeomorphism, so this is
  precisely its identity component, with the inherited open subscheme structure.
  This formulation does not need to assume finite type or a chosen group instance
  on H_red in the theorem's binders; those properties follow from H being a closed
  subgroup of A. The component is neither an arbitrary connected scheme nor a set
  of rational points.
- Universal divisor identity: on A times the scheme `Over.mk (U.ι ≫
  (GrpObj.reduced H).hom)`, the final equality is `F.comap μ = F.comap p1`.
  Here μ is explicitly the sum of p1 and p2 followed by the canonical inclusion
  `Over.homMk U.ι ≫ GrpObj.reducedι H ≫ i`. Equality of these ideals is exactly
  equality of effective Cartier divisors. The projection is flat over a field and
  μ is its composite with an isomorphism, so these are effective Cartier pullbacks;
  no choice of an isomorphism of associated line bundles replaces divisor equality.

Recorded dependency declarations read and used:

- `Field` (`Mathlib.Algebra.Field.Defs`) and `IsAlgClosed`
  (`Mathlib.FieldTheory.IsAlgClosed.Basic`), the algebraically closed clause of
  the algebraic-closure dependency (not a chosen algebraic closure of another field).
- `AlgebraicGeometry.IsAbelianVariety`
  (`WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`), together with the
  existing `CategoryTheory.GrpObj` encoding of a group scheme over k.
- `AlgebraicGeometry.IsClosedImmersion`
  (`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, publicly re-exported by
  the group-scheme dependency).
- `AlgebraicGeometry.IsClosedSubgroupScheme`
  (`WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`), one of the declarations
  recorded for def-sc-group-scheme-subgroup.
- The Cartier-ideal interface behind def-pc-divisor-line-bundle:
  `Scheme.IdealSheafData.IsInvertible`,
  `IsEffectiveCartierCenter`, and `isEffectiveCartierCenter_iff_isInvertible_ker`,
  publicly available from `WeilConjectures.AlgebraicGeometry.EffectiveCartier`.
  The recorded dual-toModules theorem and its full signature/docstring were read;
  the associated line bundle is not needed in this statement.
- `Scheme.IdealSheafData.comap` and `radical` are the existing Mathlib pullback and
  radical of ideals, not new definitions. `GrpObj.reduced`, `reducedι`, and
  `onePoint` are the existing group-scheme reduction and identity interfaces in
  `GroupScheme.Reduced` and `GroupScheme.Basic`.

The recorded proof-dependency modules for closedSubgroup_reduced_identityComponent,
IsAbelianVariety.geometricallyIntegral, smooth_geometrically_normal,
product_irreducibleComponents_bijOn_image, Scheme.Hom.denseRange_fieldPoints,
and IdealSheafData.IsInvertible.comap_of_flat are imported with plain `import`.
The factorization-locus and normal-domain-principal-divisor-kernel proof nodes have
no recorded declaration; they therefore have no import yet. They are only proof
inputs, not missing notions needed to type this statement. The full eight-step
DAG proof is included in the theorem docstring.

Source checked: `pdftotext -f 42 -l 43` of
`literature/milne-algebraic-groups_iAG2017.pdf`, printed pp.30-31, including
Proposition 1.79 and Corollaries 1.80-1.81. The transporter intersection represents
scheme-theoretic equality; the source explicitly checks all algebra extensions.
The divisor assertion is the node's stated agent-written auxiliary argument,
not misattributed to Milne Corollary 1.81. The current blueprint directory was
searched; this auxiliary has `blueprint.is = null`, so no blueprint unit statement
is being altered.

Edge cases checked before writing: Z empty or all of A gives the whole stabilizer;
the empty test scheme has a unique morphism and the unique lifting condition holds;
nonreduced Z and T retain their nilpotents through ideal comap; H is not assumed
smooth; characteristic p is unrestricted; F the zero divisor has unit ideal and
empty reduced support, with both pullbacks equal to the unit ideal; dimension-zero
A is allowed. No nonempty, positive-dimension, or reducedness hypothesis was added.
All schemes use the same arbitrary universe as the base field, following the
project's scheme-size convention.

Searches for an existing statement:

- msearch.py leanfinder: "The scheme theoretic translation stabilizer of a closed
  subscheme of an abelian variety is a closed subgroup scheme". Eight results,
  including fixingSubgroup_isClosed, instIsClosedImmersionLiftCoborder,
  IsClosedImmersion.instSubschemeι, and abstract additive stabilizers. No match.
- msearch.py loogle: `"stabilizer"`. Twelve results, including
  AddAction.stabilizer and MulAction.stabilizer. These concern abstract actions,
  not representability of the scheme functor. No match.
- msearch.py grep: `stabilizer|transporter`, Mathlib/AlgebraicGeometry. Zero hits.
- rg of Mathlib/AlgebraicGeometry for the same expression: zero hits. rg of
  WeilConjectures, Sheaf and dag/lean_names_upstream.json for
  `closed_translation_stabilizer|translation_stabilizer|translationStabilizer`:
  no existing declaration. Broader closed-stabilizer searches found only linear
  subspace stabilizers and downstream proof references; different notions.
- Exact node-id search in WeilConjectures: no hit. In Sheaf, PolarizationCalculus
  cites this node in its docstring; it does not state the stabilizer theorem.

Validation: prescribed scompile.py on the delivered module passed in sandbox mode
(1.8 s) and library mode (1.9 s), with no errors or warnings. All binders and the
universe are explicit; no diagnostics or local notation remain.

## Second reading by Q143

I re-read the node against the completed signature, separately checking every clause
listed above. In particular, the second clause has a fixed S-point and unique lift
to H times S; the divisor equality is an ideal equality on the whole product, not
rational-point invariance; the component is an actual open subscheme of H_red.
No mismatch or correction was found. This is a worker self-check, not an independent
reader claim: the dispatch brief prohibits starting other agents and assigns the
independent reading to the maintainer.
