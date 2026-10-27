## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeTorusBimultiplicativeVanishing` states
`AlgebraicGeometry.relativeTorus_bimultiplicative_eq_one`. Its only proof is `sorry`.
No definition, auxiliary theorem, or new node is introduced. The natural-language
statement and proof are unchanged. The item gains the already landed statement
dependency `def-sfb-relative-split-torus`, whose real construction supplies G_m
by `relativeSplitTorus S 1`; no second multiplicative group is defined.

Source checked directly: Brian Conrad, Reductive group schemes,
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf,
Proposition 4.3.1, proof, printed p.127 (PDF page index 126). The paragraph about
the commutativity of D' gives precisely the arbitrary-base pairing assertion.
The current blueprint direct-images proof (3) was also read; the supporting
ancestry is unchanged. No source-based correction or dispute is needed.

Clause-by-clause correspondence:

- Arbitrary scheme S: `(S : Scheme.{u})`. There is no affineness, nonemptiness,
  field, Noetherian, characteristic, or finiteness restriction on the base.
- An S-group scheme: `(Z : Over S) [GrpObj Z]`. The slice structure contains
  the structure morphism and the group object includes the identity,
  multiplication, inverse, and group identities.
- Commutativity of Z: `[IsCommMonObj Z]`, together with the preceding group
  object. This is a property of its scheme multiplication, not just of geometric
  points.
- S-separatedness: `[IsSeparated Z.hom]`; its Mathlib definition is exactly
  `IsClosedImmersion (pullback.diagonal Z.hom)`. Thus the node's recorded
  closed-immersion declaration is used through the standard separatedness API.
- G_m(T) = Gamma(T,O_T)^units, with multiplication: the group scheme
  `(relativeSplitTorus S 1).X`. Its existing construction is the Hopf spectrum
  of Gamma(S)[Fin 1 -> Z], pulled back along S.toSpecGamma. Evaluation on a
  test scheme is Hom over S; the rank-one group-algebra generator can be sent
  to any unit, and its group-like coproduct gives multiplication of those units.
  No chosen isomorphism or arbitrary group law is assumed.
- The S-morphism b from G_m x_S G_m to Z: the binder
  `(b : (relativeSplitTorus S 1).X ⊗ (relativeSplitTorus S 1).X ⟶ Z)`.
  The Cartesian tensor in Over S is the fibre product over S. The arrow is an
  ordinary scheme morphism over S, not a group homomorphism on the product.
- Multiplicativity in the first argument after every base change: `hleft`
  quantifies over every `T : Over S` and all its sections `a a' c`, and states
  `lift (a * a') c ≫ b = (lift a c ≫ b) * (lift a' c ≫ b)`.
- Multiplicativity in the second argument after every base change: `hright`
  quantifies over every `T : Over S` and `a c c'`, and states the analogous
  identity with `lift a (c * c')`. These hypotheses apply to non-affine and
  nonreduced tests, not merely field-valued points.
- Conclusion: for every `T : Over S` and `a c : T ⟶ G_m`,
  `lift a c ≫ b = 1`. The Hom group unit is T's structure map followed by
  Z's identity section, so this says exactly b(a,c)=1.
- The node's preliminary explanations of G_a, fppf group sheaves and central
  exact sequences are background terminology; no G_a or central extension is
  an object or hypothesis of this pairing statement. They are not replaced by
  additional hypotheses. Fppf locality is used in the proof plan only; the
  sheaf property of representable functors is available from Mathlib.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (def-pc-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (def-weil-closed-immersion).
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`:
  `AlgebraicGeometry.IsSeparated`, with its closed-diagonal field.
- `Sheaf.AlgebraicGeometry.RelativeSplitTorus`:
  `AlgebraicGeometry.relativeSplitTorus` (def-sfb-relative-split-torus).
  Its full definition and docstring were read, as was its DAG node.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `GrpObj`,
  `IsCommMonObj`, and the scoped `CategoryTheory.Hom.group` / `Hom.commGroup`
  structures on Hom sets. `CartesianMonoidalCategory.lift` evaluates the pairing.

The proof-dependency modules already stated are imported without `public`:
`Sheaf.AlgebraicGeometry.RingDiagonalizableGroup` (ringDiagonalizableGroup and
ringDiagonalizableGroupMap), `Mathlib.AlgebraicGeometry.Sites.Fpqc`
(fppfTopology, fppfPrecoverage_le_fpqcPrecoverage, subcanonical fpqcTopology),
`Mathlib.CategoryTheory.Sites.LocallyBijective`
(GrothendieckTopology.W_iff_isLocallyBijective),
`Mathlib.CategoryTheory.Sites.Localization` (GrothendieckTopology.W_iff), and
`Mathlib.RingTheory.AdjoinRoot` (AdjoinRoot.powerBasis'). The affine-spectrum
and closed-immersion-base-change dependencies are already provided by the
public Mathlib imports. `lem-sfb-relative-diagonalizable-character-duality`
has no Lean statement or Mathlib match and therefore has no import yet; it
is a proof prerequisite only, not an absent notion needed to type this statement.
Every proof step, including that prerequisite, is retained in the theorem docstring.

Edge cases checked before writing: empty S and empty test T have unique arrows;
there is no Nonempty assumption. The trivial target is included. Nonreduced
bases and tests are included, e.g. dual numbers over F_p. Positive characteristic
and torsion orders divisible by it are retained, since no integer-invertibility
hypothesis occurs. Tests have the same scheme universe as S and the represented
objects; the test universe cannot fall below the base's universe. This is the
standard unrestricted Yoneda encoding in this category; the universal product
itself is among its tests. No data definition contains a postponed proof.

Searches for an existing statement:

- `msearch.py leanfinder`, query "A bimultiplicative morphism from two
  multiplicative group schemes over any scheme to a separated commutative group
  scheme is trivial": eight hits, on trivial categorical group objects,
  Hom.commGroup and separatedness; none states the pairing theorem.
- `msearch.py loogle`, query `"Scheme", "pairing"`: zero hits.
- `msearch.py grep`, query `bimultiplicative|biadditive|torsion.*[Dd]ense`,
  Mathlib/AlgebraicGeometry: zero hits.
- `msearch.py leansearch`, query "Every bimultiplicative morphism of two
  multiplicative group schemes to a separated commutative group scheme is
  trivial": eight hits, concerning linear pairings and separatedness, no match.
- `rg` for `bimultiplicative|Bimultiplicative|biadditive|Biadditive` in both
  lean/WeilConjectures and lean/Sheaf found only unrelated algebraic/adic pairings.
  The exact node-id search in lean/WeilConjectures found no existing declaration.
- Searches of the group-scheme and relative-torus modules located the already
  landed RelativeSplitTorus. Its DAG record supplies the existing construction;
  field-only StandardGroupSchemes.multiplicative is not used.
- Search for the chosen declaration name in Mathlib, lean/Sheaf and
  dag/lean_names_upstream.json found no clash.

Validation: prescribed scompile.py compiled both its sandbox and its actual module
name on the live server, cleanly (1.4 seconds each). Every variable and the universe
are explicitly bound; both auto-implicit options are disabled. Delivery dry run
and final delivery are performed with deliver2.py.

## Second reading by Q143

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
