## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.AffineToAbelianHomVanishing` states
`AlgebraicGeometry.affine_to_abelian_hom_vanishing`, with `sorry` as its sole proof.
It introduces no definition and changes only the item's `lean` field.

Hypotheses and clauses, matched individually:

- The field k is `{k : Type u} [Field k]`, and algebraic closedness is `[IsAlgClosed k]`.
- The k-group schemes L and A are `(L A : Grp (Over (Spec (.of k))))`.
  `Grp` supplies the group structures, and `Over` supplies their structure morphisms.
- Smoothness of L/k is `[Smooth L.X.hom]`.
- Connectedness of L is `[ConnectedSpace L.X.left]`, which includes nonemptiness.
- Affineness of L is `[IsAffine L.X.left]`. Mathlib's canonical isomorphism with
  Spec of global sections expresses precisely the node's existence of an affine spectrum.
- Finite type of L/k is `[LocallyOfFiniteType L.X.hom] [QuasiCompact L.X.hom]`,
  following the recorded finite-type dependency's convention.
- L need not be commutative: there is no `IsCommMonObj L.X` binder.
- A/k is an abelian variety by `[IsAbelianVariety A.X]`; its group structure is
  already supplied by the bundled A. The class means proper, smooth and connected.
- An arbitrary k-group homomorphism is `(f : L ⟶ A)`, a bundled group-object morphism.
  Its underlying map over k is `f.hom.hom` and its underlying scheme map is
  `f.hom.hom.left`.
- The conclusion is `f.hom.hom.left = L.X.hom ≫ (η[A.X]).left`.
  Here `L.X.hom` is the structure map to Spec k and `(η[A.X]).left` is the identity
  section Spec k → A. Mathlib's Cartesian structure on `Over` has tensor unit
  `Over.mk (𝟙 (Spec (.of k)))`, so the right-hand side has exactly the stated source
  and target. This is equality of scheme morphisms, not just equality on k-points;
  the faithful forgetful functors make it equivalent to equality of homomorphisms.
- L = 1 and A = 1 remain allowed; neither positive dimension nor nontriviality is assumed.

Dependency declarations used, after reading their definitions and docstrings:

- `Mathlib.Algebra.Field.Defs`: `Field` (through the public field-theory import).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraic-closedness
  component explicitly named by def-weil-algebraic-closure's Mathlib match.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.Grp`, `CategoryTheory.GrpObj`,
  the group-object morphisms, and `Grp.hom_ext`; `IsMonHom` and `MonObj.one` are in
  `Mathlib.CategoryTheory.Monoidal.Mon`, publicly available through this module.
  This is def-sc-group-scheme's recorded interface, also documented in the public
  import `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `QuasiCompact` is defined in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `IsAffine` in `Mathlib.AlgebraicGeometry.AffineScheme` is available through GroupScheme.Defs.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety` with its full proper/smooth/connected signature.
- def-weil-pbc-scheme-conventions explicitly collects conventions without defining
  a new notion; its finite-type and affine conventions are rendered as above.

The file also imports all recorded proof-dependency modules: group separatedness,
homomorphism factorization, affine normal quotients, sheafification, fpqc descent,
Yoneda, closed-immersion properness, proper-affine finiteness, smooth geometric
reducedness, connectedness/idempotents, and the reduced finite algebra criterion.
These are plain proof imports; statement dependencies are public imports.
The theorem docstring carries all six steps of the node's proof and names the inputs.

Source checked: Milne, Algebraic Groups (2017), the local PDF, Theorem 5.39 and
Remark 5.40 (printed pp.108–109), Proposition 8.1(b) and Example 8.4 (printed p.149).
The former gives the scheme-theoretic image factorization, the latter makes its
smooth connected affine image in an abelian variety trivial. No source correction
or disputed statement was needed.

Edge cases checked before writing: the trivial source and target, arbitrary
characteristic, noncommutative source, and a possibly nonreduced kernel. No
smoothness assumption on the kernel is introduced. An empty scheme cannot be a
group scheme over a field because it cannot have an identity section, consistently
with ConnectedSpace including nonemptiness. Equality is on scheme morphisms, so
no nonreduced test scheme is lost. The universe u is arbitrary and shared by the
field and schemes in the project's standard Scheme/Spec encoding.

Searches actually run:

- `msearch.py ... leanfinder "Every homomorphism from a smooth connected affine algebraic
  group to an abelian variety is trivial"`: eight hits, concerning trivial abstract
  commutative group objects, affine-space morphisms and abstract abelianization;
  none states the algebraic-group assertion.
- `msearch.py ... loogle "IsAbelianVariety, IsAffine"`: zero hits; the service reports
  unknown identifier `IsAbelianVariety` (the project notion is outside its index).
- `msearch.py ... leansearch "A homomorphism from a connected affine group scheme to an
  abelian variety is zero"`: eight hits on abstract zero homomorphisms or elliptic
  curve point maps, no matching scheme theorem.
- `msearch.py ... grep "affine.*abelian|abelian.*affine|AbelianVariety" AlgebraicGeometry`:
  four hits in AffineEtale on abelian sheaf categories, no match.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for affine/abelian combinations,
  `affine_to_abelian_hom_vanishing`, and the exact item id: no matching statement;
  unrelated affine sheaf/cohomology results are not this assertion.
- The declaration-name search also included `dag/lean_names_upstream.json`: no clash.

Validation: scompile.py compiled the module separately in sandbox and library modes,
without errors or unexpected warnings, both before and after the final public-import
adjustment. The current latest blueprint direct-image stability proof (3) was also
read: this is an inherited lower-level prerequisite and changes no unit statement.

## Second reading by Q93

A separate pass by this same dispatched worker reopened the node and final module;
the maintainer supplies the independent review, as specified in the assignment.
I checked all binders against the node: algebraically closed field, both group
schemes, smooth/connected/affine/finite-type source, abelian target, arbitrary
homomorphism. Each appears exactly as mapped above. In particular, there is no
commutativity condition on L, no separability condition, and no assumption on its
kernel. I checked that the target group instance is supplied by `Grp`, separately
from `IsAbelianVariety`, whose definition deliberately does not carry group data.
I read the tensor-unit and `toUnit_left` declarations for `Over` to verify that
`(η[A.X]).left` is a section with domain Spec k. The conclusion consequently reads
exactly f = e_A composed with p_L, including the two trivial-group cases. No
mathematical mismatch was found; the only adjustment was to list the recorded
statement-dependency modules directly as public imports.
