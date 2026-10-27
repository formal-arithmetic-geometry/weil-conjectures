## Worker report

The module `Sheaf.AlgebraicGeometry.SemiabelianNeronLftExistence` states
`AlgebraicGeometry.semiabelian_neron_lft_existence` with a `sorry` proof.  It uses
`Grp (Over (Spec (.of F)))` for the smooth separated commutative finite-type group
scheme over the fraction field and `Grp (Over (Spec (.of R)))` for the model.  The
fraction-field restriction is the canonical group-object functor
`(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).mapGrp`.

The hypotheses render as follows. `R : Type u` with `[CommRing R] [IsDomain R]
[IsDiscreteValuationRing R]` is the discrete valuation ring; `F : Type u` with
`[Field F] [Algebra R F] [IsFractionRing R F]` is its fraction field.  `P` is the
commutative group scheme over `Spec F`; `[Smooth P.X.hom]`, `[IsSeparated P.X.hom]`,
`[LocallyOfFiniteType P.X.hom]`, and `[QuasiCompact P.X.hom]` express smoothness,
separatedness, and finite type. `hP : HasSemiabelianGeometricFibres P` is the
semiabelian geometric-fibre hypothesis.

The conclusion has a model `N` over `Spec R`, with `IsCommMonObj N.X`, smoothness,
separatedness, and `LocallyOfFiniteType N.X.hom`; no finite-type or quasi-compact
condition is imposed on `N`.  The isomorphism `α` is between the canonical generic
base change of `N` and `P`.  The first `Function.Bijective` quantifies over every
smooth `X : Over (Spec R)` and sends an underlying morphism `f : X ⟶ N.X` to its
generic restriction followed by `α`.  The second quantifies over every smooth
commutative group scheme `X` over `Spec R` and sends a group morphism `f : X ⟶ N`
through the same generic restriction and `α`; it is exactly the restriction of the
first bijection to group homomorphisms.

The statement dependencies used are:

- `def-sc-discrete-valuation-ring`: Mathlib `IsDiscreteValuationRing` in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`.
- `def-weil-affine-spectrum`: Mathlib `AlgebraicGeometry.Spec` in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-sbc-smooth-morphisms`: Mathlib `AlgebraicGeometry.Smooth`.
- `def-weil-closed-immersion`: Mathlib `AlgebraicGeometry.IsClosedImmersion`; the
  separatedness class is Mathlib `AlgebraicGeometry.IsSeparated`.
- `def-pc-base-change`: canonical `CategoryTheory.Over.pullback` and
  `CategoryTheory.Functor.mapGrp` (the recorded source declaration is
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, whose base-change
  conventions are compatible with this use).
- `def-sfb-semiabelian-geometric-fibres`: `AlgebraicGeometry.HasSemiabelianGeometricFibres`
  from `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`.
- `def-weil-finite-type-morphism`: Mathlib `LocallyOfFiniteType` and `QuasiCompact`.

Edge cases checked: rank-zero torus is allowed by `HasSemiabelianGeometricFibres`;
`N` is only locally of finite type, so the multiplicative-group lft example is not
excluded; arbitrary residue characteristic and imperfect residue fields are not
introduced as hypotheses; and the universal property includes all smooth test
schemes, including the empty scheme, while the group clause separately includes the
trivial group scheme.

Searches made: `msearch.py ... leanfinder "A geometrically semiabelian group over the
fraction field of a discrete valuation ring admits a Neron model locally of finite
type"` returned only elliptic-curve reduction and general smoothness declarations;
`msearch.py ... leansearch "Neron locally finite type model smooth mapping property
semiabelian variety"` returned only `LocallyOfFiniteType`, `Smooth`, and related
finite-type declarations; `msearch.py ... loogle '"Neron"'` returned zero hits;
`msearch.py ... grep 'Neron|Néron|semi.?abelian' AlgebraicGeometry` returned zero
Mathlib hits.  Repository searches with `rg` found no existing Néron-model
statement.  The source is Bosch–Lütkebohmert–Raynaud, *Néron Models* (1990),
10.1 Definition 1 and 10.2 Theorem 2 (printed pp. 289, 297).

No `STATEMENT-DISPUTED` flag or node correction is needed.

## Second reading by NQ

I reread the node and the module.  The DVR and fraction-field hypotheses, smooth
separated commutative finite-type generic group, semiabelian fibres, smooth separated
locally-finite-type model, generic-fibre group isomorphism, all-smooth-scheme mapping
bijection, and group-homomorphism restriction are each present.  The module imposes no
completeness, excellence, residue-field perfection, or finite-type hypothesis on `N`.
The canonical `Over.pullback.mapGrp` construction is used for both generic restriction
maps, so the Lean objects match the node's base-change objects.  No mismatch was found.

The stated proof dependencies are imported with plain `import` visibility, including
Mathlib's PID, rational-root/normality, DVR dimension, integral-closure, and free-module
results and the six recorded project modules. The proof-only nodes without a Lean
record (torsor representability, abelian Néron existence, hom-vanishing, split-torus
Néron extension, and finite-flat Néron descent) have no import to add yet. The
separatedness predicate is defined by a closed-immersion diagonal. The base-change
source module is already publicly reachable through the semiabelian dependency.

Validation: `scompile.py` compiled the theorem in sandbox and library module mode.
The first dry run caught an extra `:=` delimiter in the signature metadata; the
record now ends immediately before that delimiter, as the preflight reader expects.
The proof docstring records every accepted proof step rather than only the overview.
The source scan was read online at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf;
10.1 Definition 1 drops finite type and retains the smooth mapping property, and
10.2 Theorem 2 gives the no-additive-subgroup criterion over an arbitrary DVR.
