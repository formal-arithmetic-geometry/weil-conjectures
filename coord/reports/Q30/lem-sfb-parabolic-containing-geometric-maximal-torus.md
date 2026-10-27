## Worker report

Item: `lem-sfb-parabolic-containing-geometric-maximal-torus`, group Q30, stage 2.
The module `Sheaf.AlgebraicGeometry.GroupScheme.ParabolicContainingGeometricMaximalTorus`
states `AlgebraicGeometry.exists_geometricMaximalTorus_containing_in_parabolic`.
Its only theorem has proof `sorry`; there are no new definitions or auxiliary theorems.
The node is unchanged except for its `lean` record.

The node-to-Lean correspondence is as follows.

- Any field k: `{k : Type u} [Field k]`, with `u` explicitly declared and
  `autoImplicit` disabled. There is no characteristic, finiteness, infinitude or
  perfectness restriction.
- Group schemes G, P and D: `G P D : Grp (Over (Spec (.of k)))`. Bundling supplies
  the multiplication, identity and inverse and their identities, and all arrows
  between these objects are group-scheme homomorphisms.
- Reductive G: `hG : ReductiveTorusCentralizer.IsReductive G`, exactly the recorded
  dependency. Its definition asserts affine finite type, smoothness, connectedness
  after algebraic closure, and triviality of each smooth connected normal closed
  unipotent subgroup after algebraic closure. Its unipotence predicate is the
  recorded smooth faithful-matrix geometric-point predicate.
- Closed subgroup P of G: `iP : P ⟶ G` and
  `hP : IsClosedSubgroupScheme iP.hom.hom`. This includes the underlying scheme
  closed immersion and the pointwise subgroup condition, with no normality condition.
- Smooth P: `hPsmooth : Smooth P.X.hom`.
- Geometrically connected P: `hPconnected : ConnectedSpace
  ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj P).X.left`.
  Connectedness after the chosen algebraic closure is the usual algebraic-closure
  test for geometric connectedness, as in the recorded reductivity definition.
- Representable proper finite-type fppf right-coset sheaf G/P: `hquot` asserts
  existence of `Q : Over (Spec (.of k))` with `IsProper Q.hom`,
  `LocallyOfFiniteType Q.hom`, `QuasiCompact Q.hom`, and `Presheaf.IsSheaf` for
  `Scheme.fppfTopology.over (Spec (.of k))` on `yoneda.obj Q`. The parallel
  arrows are `yoneda.map (fst G.X P.X)` and
  `yoneda.map (lift (fst G.X P.X) (snd G.X P.X ≫ iP.hom.hom) ≫ μ[G.X])`.
  They send `(g,p)` to `g` and `g iP(p)`. Their presheaf coequalizer therefore has
  exactly the right-coset sections on each test scheme. The arrow `ηq` to
  `yoneda.obj Q`, together with bijectivity of precomposition into every sheaf
  `Z`, states precisely sheafification, rather than presheaf representability or
  a quotient in group schemes. This is the same presentation used by the recorded
  homogeneous-quotient dependency. Affine schemes are a basis for this fppf site;
  restriction gives the node's algebra test objects and faithfully flat finitely
  presented affine coverings. No reducedness assumption on a test algebra occurs.
  A separate quotient-map binder and equation are unnecessary: its canonical map
  is recovered by composing `coequalizer.π` with `ηq` and applying Yoneda.
- Closed torus D in P, without splitting: `iD : D ⟶ P`,
  `hD : IsClosedSubgroupScheme iD.hom.hom`, and
  `hDtorus : MultiplicativeType.IsTorus D`. The recorded torus definition becomes
  a finite product of the recorded multiplicative group after algebraic closure.
- Existence of a closed torus T in P: the existential `T` and `iT : T ⟶ P`,
  followed by `IsClosedSubgroupScheme iT.hom.hom ∧ MultiplicativeType.IsTorus T`.
- Containment of the prescribed D, compatible with its original inclusion:
  `∃ j : D ⟶ T, j ≫ iT = iD`. Since `iD` and `iT` are closed inclusions,
  this factorization is itself the closed subgroup inclusion of D in T.
- Ambient geometric maximality for every algebraic closure: the final universal
  quantifier `(F : Type u) [Field F] [Algebra k F] [IsAlgClosure k F]` and
  `ReductiveTorusCentralizer.IsMaximalTorus
  ((MultiplicativeType.baseChange (K := F)).map (iT ≫ iP))`.
  The composition embeds in G, so maximality is in G_F, not merely P_F.
  `IsAlgClosure` means algebraic and algebraically closed, exactly an algebraic
  closure. The single torus T and its factorization are chosen before F.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, bundled as
  `CategoryTheory.Grp`; the specialization and subgroup interfaces are documented
  in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive` and `IsMaximalTorus`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `AlgebraicGeometry.MultiplicativeType.IsTorus`, `baseChange`, `splitTorus`;
  `Sheaf.AlgebraicGeometry.SolvableGroupStructure`: `IsAlgebraic`, `IsUnipotent`
  as the already used constituents of reductivity. These are exposed by the
  terminology dependency, with no copies in this delivery.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, through `IsClosedSubgroupScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
  Finite type is their conjunction, as recorded by the dependency node.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`.
- The quotient presentation uses the existing categorical `coequalizer`,
  `yoneda`, `Presheaf.IsSheaf`, `Sheaf`, and `Scheme.fppfTopology`, rather than
  defining a new quotient or a new parabolic predicate.

All already stated proof-dependency modules are imported: largest subtori,
Borel conjugation cover, homogeneous quotient geometry and Borel maximal-torus
conjugacy. Proper/smooth base-change instances are available from the public
proper and reductive-terminology imports. The dimension/product lemma,
maximal-torus field-extension lemma and solvable proper fixed-point lemma have
no recorded Lean module in the read state, so no import can yet be added for
those proof dependencies. The docstring retains all four proof steps, including
those three pending proof ingredients.

Edge cases checked before writing and in the rereading:

- Rank-zero D is admitted by the recorded `IsTorus` definition (`n = 0`), and
  the factorization expresses its retained inclusion. No positive rank occurs.
- P = G is permitted: there is no proper-containment hypothesis. Its quotient
  is the base point, a proper finite-type scheme.
- The trivial ambient reductive group and rank-zero T are permitted.
- Finite and imperfect fields are admitted; the greatest-dimension choice and
  scalar-extension argument impose neither infinitely many rational points nor
  perfectness. D need not split over k.
- Nonreduced test algebras remain present in the fppf quotient condition.
- The universe `u` is arbitrary and shared by the field, schemes and test
  algebras, following the recorded group-scheme and scalar-extension APIs.
  An algebraic closure can always be realized at this size, and larger models
  are isomorphic over k to such a model. No geometric field is excluded up to
  the scalar-extension isomorphism relevant to maximality.

Source read: local Milne PDF, Theorem 17.82 and Corollary 17.83 (p.379),
Theorem 17.10 and the paragraph after Definition 17.12 (pp.354--355),
Definition 17.15 and Theorem 17.16 (p.356), and the converse of Theorem 25.1
(p.544). These support exactly the node's prescribed-torus extension argument.
No statement fault or `STATEMENT-DISPUTED` issue was found.

Searches for an existing statement (all returned no matching group-scheme result):

- `msearch.py`, LeanFinder: "A torus in a parabolic subgroup of a reductive
  algebraic group extends to a geometrically maximal torus". Eight hits, concerning
  Cartan subalgebras, root pairings and Lie algebras; none is this statement.
- `msearch.py`, Loogle: `"IsTorus", "IsParabolic"`. Zero hits.
- `msearch.py`, grep in Mathlib/AlgebraicGeometry:
  `maximal.*torus|torus.*maximal|IsParabolic`. Zero hits.
- `msearch.py`, LeanSearch: "Every torus in a parabolic subgroup is contained in
  a geometrically maximal torus". Eight hits, concerning parabolic matrices,
  abstract groups, topological tori and matroids; none is this statement.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`:
  `IsParabolic|parabolic.*torus|torus.*parabolic|parabolic_containing_geometric`.
  Only a proof-text mention in SplitReductiveCharacteristicSequence; no existing
  theorem or parabolic predicate. A wider search of the algebraic-geometry
  directories found cocharacter limit functors and standard-parabolic geometry,
  not this theorem or an arbitrary-parabolic definition.
- `rg` for the exact node id in `lean/WeilConjectures`: no match.

Validation: the prescribed `scompile.py` succeeded for the single delivered file,
in both its sandbox and its library module form, with no errors or unexpected
warnings. Delivery dry-run and push results are recorded below after execution.

## Second reading by Q30

This is the dispatcher's single-worker rereading; the maintainer performs the
independent review on delivery. I reread the node and final signature together.
The supplied D is a torus over k and is retained by `j ≫ iT = iD`. The inclusion
whose scalar extension is maximal is `iT ≫ iP`, so the ambient object is G.
The existential precedes the universal quantifier over algebraic closures.
The parabolic condition retains smoothness, geometric connectedness, closedness,
and a proper finite-type representing scheme for the fppf sheafification of right
cosets; it asserts neither normality of P nor an unsheafified quotient. The
coequalizer's second map is right multiplication by iP(p), which verifies the
coset orientation. Reductivity and tori use the dependency definitions, including
rank zero. No extra affine, finite-type, splitting or characteristic hypothesis
has been imposed on P or D; their inherited properties remain consequences.
No mismatch was found, and no correction or dependency replacement was needed.

Delivery dry run: `deliver2.py Q30 lem-sfb-parabolic-containing-geometric-maximal-torus
--no-push` printed `OK (dry run): commit d46420ef6dd passes the preflight and compiles;
nothing pushed`. Local packet checks confirmed only `lean` changes in the node,
exact agreement of its recorded signature with the module, maximum Lean line width
85, and exactly one theorem with one `sorry`.
