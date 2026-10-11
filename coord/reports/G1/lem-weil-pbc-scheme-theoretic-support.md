## Worker report

The module states `AlgebraicGeometry.Scheme.schemeTheoreticSupport` for a scheme `X` and a quasi-coherent finite-type module `F`. It represents the annihilator ideal sheaf by an `IdealSheafData` object `I`: on each affine open `U`, `I.ideal U` is `Module.annihilator` of the module of sections. The conjunct `IsClosedImmersion I.subschemeι` gives the closed subscheme; the support conjunct identifies its support with the nonzero-stalk locus; the next conjunct states annihilation; and the final conjunct states minimality among ideal sheaves annihilating `F`.

The hypotheses are rendered by `(X : Scheme.{u})`, `(F : X.Modules)`, `[F.IsQuasicoherent]`, and `[F.IsFiniteType]`. The affine annihilator clause is the first conjunct, the closed immersion is the second, equality with support is the third, annihilation is the fourth, and the universal minimality clause is the fifth.

Dependencies used: `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` (`AlgebraicGeometry.Scheme.IdealSheafData`, `IdealSheafData.subschemeι`), `Sheaf.AlgebraicGeometry.Coherent` (`SheafOfModules.IsQuasicoherent`, `IsFiniteType`), `Sheaf.AlgebraicGeometry.ClosedSubsetProperOver` (support convention), and Mathlib `AlgebraicGeometry.IsClosedImmersion`.

Edge cases checked: the statement permits arbitrary schemes, empty support, and zero modules; no nonemptiness or characteristic assumptions are introduced. Universes are explicit.

Searches made: node mathlib searches (LeanSearch, LeanFinder, Loogle, grep) found no annihilator ideal sheaf theorem; `rg` over existing Sheaf declarations found no scheme-theoretic-support statement. Mathlib's `IdealSheafData` and `Module.annihilator` were used directly.


## Second reading by G1

Independently read the node's statement and all seven proof steps, the Lean module,
all six statement-dependency node records, and their declarations. The repository's
literature checkout is absent on this machine; read the Stacks TeX available at
/home/ubuntu/c1-stacks-review/morphisms.tex, labels lemma-scheme-theoretic-support
(05JU), definition-scheme-theoretic-support (05JV), and
lemma-closed-immersion-bijection-ideals (01QQ). The source assumes only a scheme
and a finite type quasi-coherent module; no base, separation or Noetherian
hypothesis. The node intentionally states the annihilator formulation, omitting
05JU's auxiliary module G, as its stage-1 review explicitly records. No change
of the node's statement is needed.

Objects, hypotheses, and conclusions, item by item:

- X: `(X : Scheme.{u})`, Mathlib's Scheme (def-pc-scheme): exact.
- F: `(F : X.Modules)`, the sheaf of O_X-modules on the underlying space:
  exact. Read Coherent.lean, IsQuasicoherent in Quasicoherent.lean, and
  IsFiniteType in Generators.lean. `[F.IsQuasicoherent] [F.IsFiniteType]`
  renders precisely the two hypotheses in pqf-def-coherent; no coherence,
  finite presentation or extra instance is assumed.
- Ann(F) on every open U: the kernel ideal
  `RingHom.ker (I.subschemeι.app U).hom`, identified by the displayed iff
  with `∀ V h s, X.presheaf.map (homOfLE h).op a • s = 0`.
  This is exactly the rule in the node, including all smaller opens V.
- (1) Quasi-coherent ideal sheaf: `I : X.IdealSheafData` is the existing
  affine-data representation of such a sheaf, with localization compatibility
  as a structure field. Read Basic.lean's structure and Hom.ker, not merely
  their names. The first conjunct says `I.ideal U = Module.annihilator ...`
  on every affine open. Together with the all-open iff and ker equality this
  identifies I with the specified Ann(F), exactly.
- (2) Closed subscheme: `IsClosedImmersion I.subschemeι`, with
  `I.subschemeι.ker = I` identifies its ideal sheaf with Ann(F), using the
  recorded def-sbc-closed-immersion-ideal-sheaf declaration Hom.ker.
  Read IsClosedImmersion's closed embedding and surjective stalk fields.
  The `IsPullback (I.subschemeCover.f U) (Spec.map ... Ideal.Quotient.mk ...)
  I.subschemeι U.2.fromSpec` conjunct says its inverse image on the affine
  open is Spec of the quotient, over that same affine open. Its ideal is
  the annihilator by the first conjunct. Read Spec's signature and the
  subschemeCover construction; its domain is Spec(Γ(X,U)/I(U)). Exact.
- (3) Image/support: `Set.range I.subschemeι =
  {x : X | ¬ Subsingleton (F.presheaf.stalk x)}`. This is the node's image
  and the project's inline support convention from
  ClosedSubsetProperOverBase.lean; no properness hypothesis is imported
  into the signature. Exact.
- (4) Annihilation: for every open V, every element of
  `RingHom.ker (I.subschemeι.app V).hom`, and every section of F on V,
  `a • s = 0`. Exact, including non-affine opens.
- (5) Minimality: for every scheme Z' and map `i' : Z' ⟶ X` which is a
  closed immersion, annihilation on every open implies inclusion of its
  kernel ideals into the kernel ideals of I.subschemeι on every open.
  This is precisely ideal-sheaf inclusion in the stated direction. Exact.

Mismatches repaired: the worker's affine-data statement did not explicitly
identify the all-open annihilator rule or the immersion's kernel, omitted
clause (2)'s quotient description, and rendered (4),(5) only on affine opens.
Added the all-open iff, ker equality and quotient pullback, made the image
explicit as Set.range, and rendered annihilation and minimality on all opens
using the actual section kernels of closed immersions. No private definition
or new dependency module was necessary. The docstring lacked the seven proof
steps; added all seven with their DAG dependencies and sources, and the
standard copyright header. Synchronized lean.statement verbatim to the
new signature. The Worker report above describes the original version.

Edge cases: the empty scheme and empty open are allowed, with no nonempty
binder; the zero module has unit annihilator and empty closed support.
There is no index type, degree n, characteristic condition, field, or
Noetherian assumption. Universe u is bound explicitly throughout. A closed
subscheme of X is representable in Scheme.{u}; quantification over such
closed immersions adds no universe restriction on their intrinsic objects.
All variables in the displayed statement are bound.

Independent searches (different terms from the original worker): msearch
LeanSearch query "closed subscheme annihilating finite quasi coherent module
smallest support" returned service unavailable (recorded, no claimed result).
msearch Loogle "Module.annihilator" found the ring-module annihilator and
its algebraic lemmas, no scheme statement. msearch grep
"scheme.?theoretic.?support|annihilator" in Mathlib/AlgebraicGeometry found
only SpreadingOut's ring annihilator uses. Independently rg searched
WeilConjectures/ and lean/Sheaf for schemeTheoreticSupport, annihilator and
scheme-theoretic support. No existing statement of this node was found.
The existing IdealSheafData, Hom.ker, Spec, and Module.annihilator suffice.
Opened upstream IdealSheaf/Subscheme.lean: its
isPullback_subschemeCover_map is the general quotient-chart fact, not this
annihilator/support theorem; it confirms the chosen pullback encoding.

No new nodes, no dependency modules, no hollow definitions, no proved lemma,
and no statement correction. The single theorem's proof remains `by sorry`.
Server compilation of the complete 81-line module succeeded in 2.6 seconds
with no errors or warnings. Dry-run and delivery preflight follow below.
