## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.TorusAbelianHomVanishing`
states `AlgebraicGeometry.torus_abelian_hom_vanishing`; its sole proof is `sorry`.
No definitions or additional theorem statements are introduced.

Hypothesis and conclusion correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
  These are Mathlib's field and algebraic-closedness predicates; no chosen
  algebraic closure or extra characteristic condition is needed.
- The abelian variety over k is `(A : Over (Spec (.of k))) [GrpObj A]
  [IsAbelianVariety A]`. The existing predicate means precisely proper, smooth,
  and connected; its group structure is separately bound, as its documentation
  requires. No commutativity hypothesis is added.
- The integer r >= 0 is `(r : ℕ)`, with zero included. The existing
  `MultiplicativeType.splitTorus k r` is the actual r-fold product of the
  recorded `StandardGroupSchemes.multiplicative k`, with the unit at rank zero.
  Its `.X` is its underlying k-scheme equipped with that group structure.
- The first conjunct quantifies over every k-morphism
  `f : (MultiplicativeType.splitTorus k r).X ⟶ A` with `[IsMonHom f]`.
  Its equality says exactly that f is the structure map followed by the
  identity section, `CartesianMonoidalCategory.toUnit _ ≫ MonObj.one`.
- The second conjunct has every k-group homomorphism in the opposite direction,
  `g : A ⟶ (MultiplicativeType.splitTorus k r).X`, with `[IsMonHom g]`,
  and asserts the identical zero-map characterization with target T.
- Morphisms in `Over` are equal exactly when their underlying scheme maps
  are equal. Thus neither conjunct is merely a statement about geometric
  points. Each Hom set contains its zero map, so the two displayed universal
  equalities give precisely the equivalent trivial-Hom-group formulation.

Dependencies read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-weil-algebraic-closure`: `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic
  (the node's match explicitly names this predicate as its closed-field clause).
- `def-sc-abelian-variety`: `AlgebraicGeometry.IsAbelianVariety`,
  WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs.
- `def-sc-gm-ga`: `AlgebraicGeometry.StandardGroupSchemes.multiplicative` and
  `multiplicativeGroup`, Sheaf.AlgebraicGeometry.StandardGroupSchemes, publicly
  imported through the split-torus definition.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, `IsMonHom`, and `MonObj.one`,
  Mathlib.CategoryTheory.Monoidal.Grp / Mon, with the k-scheme interpretation
  read in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs (publicly reached
  from StandardGroupSchemes).
- The already landed `def-sfb-tori-multiplicative-type` is added to stmt_deps
  to use `AlgebraicGeometry.MultiplicativeType.splitTorus`, from
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType, rather than duplicate finite
  products or define another split torus. No existing statement is corrected.

All recorded proof-dependency modules are imported privately where available,
with Mathlib modules providing the matched affine, proper, separated,
closed-immersion, affine-target and fibre-product facts. Public statement
imports expose the standard group and algebraically closed field APIs.

Edge cases checked against the definitions and source: rank zero is the
trivial group scheme, so both directions have only the identity-section map;
rank one is the recorded Laurent multiplicative group; a zero-dimensional
abelian variety is allowed. The scheme A cannot be empty (it is connected
and has an identity section). No positive dimension, positive rank,
characteristic-zero, separability, or kernel-smoothness assumption is imposed.
The universe u is explicit, as are all variables; autoImplicit is disabled.
The theorem is valid in positive characteristic, including inseparable maps:
the proof uses affine normal quotients without requiring a smooth kernel.

Source read: literature/milne-algebraic-groups_iAG2017.pdf, Proposition 8.1(b)
and Example 8.4 (printed p.149), and Section 8(e) (printed p.151), using
pdftotext. These give respectively affine smooth connected quotients, the
triviality of affine smooth connected closed subgroups in a complete group,
and trivial homomorphisms from complete connected groups to affine groups.
The docstring reproduces every step of the node's factorization/global-sections
proof and cites the matching DAG inputs.

Searches actually run via batch2/msearch.py for Q50 and this item:

- LeanFinder: "Every homomorphism between a split algebraic torus and an abelian
  variety is zero in both directions": eight hits (algebraic field homomorphisms,
  abstract characters, root data, trivial-group Hom); no exact theorem.
- Loogle: `"IsAbelianVariety"`: zero hits.
- Mathlib grep: `AbelianVariety|torus|Torus`, AlgebraicGeometry: zero hits.
- LeanSearch: "A homomorphism of group schemes between an algebraic torus and
  an abelian variety is trivial": eight hits, including abstract group kernels,
  Scheme.Hom, and Grp.uniqueHomFromTrivial; no exact theorem.
- rg of lean/WeilConjectures and lean/Sheaf for the item id and
  `torus.*[Aa]belian|[Aa]belian.*torus|torus_abelian`: no existing vanishing
  declaration. Related semiabelian results do not state this theorem.
- rg for `def splitTorus|abbrev splitTorus` in both project trees found
  ToriMultiplicativeType and SplitTorusOverRing. The former is the exact field
  construction built from the recorded G_m and is reused. Its full definition
  and docstring were read; no new node is necessary.

No STATEMENT-DISPUTED flag or statement correction is needed. The example
Sheaf.CategoryTheory.CompactObject is withdrawn; its node now points to
WeilConjectures.CategoryTheory.CompactObject, whose module header and docstrings
were also read as the current example.

## Second reading by Q50

The dispatcher forbids spawning agents; this is the worker's second reading,
with the node, source text, definition modules and theorem open. The maintainer
will perform the independent review described in the assignment.

On rereading, the two conjuncts retain both directions and explicitly quantify
only group homomorphisms, rather than arbitrary scheme maps. The `Over` category
retains the k-structure. The target identity section is selected by `MonObj.one`
in each equality; `toUnit` is the unique map to Spec k. `IsAbelianVariety` has
all three and only the three geometric conditions of its node, and its separate
GrpObj binder was checked against its documentation. The recursively defined
split torus is exactly a product of the recorded G_m, including the empty
product. Adding its existing definition node to stmt_deps avoids a private
construction. All quantifiers and universe binders are explicit. No mismatch
or mathematical change was found.

Validation: prescribed scompile.py compiled the delivered module successfully
in both its sandbox and library module modes, with no errors or unexpected
warnings. The library-mode compile reported 1.8 seconds.
