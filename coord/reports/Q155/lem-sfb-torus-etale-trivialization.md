## Worker report

The module `Sheaf.AlgebraicGeometry.TorusEtaleTrivialization` states
`AlgebraicGeometry.torus_etale_trivialization`, with its sole proof `sorry`.
It adds no definitions, dependency repairs, new nodes or statement changes.
The existing node has no released repair note. Its accepted six-step proof is
included, with every cited node, in the theorem docstring.

Source read: Brian Conrad, *Reductive group schemes*, Proposition B.3.4,
printed pp.291–292 (PDF pages 290–291, zero based), online at
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf.
The proposition explicitly allows an arbitrary scheme S and upgrades fppf-local
finite-type diagonalizability to étale-local diagonalizability. The torus case
uses the finite free character lattices of the initial split tori, as in the
node's accepted splitting-isomorphism-functor argument. No henselian or
Noetherian restriction is imported from the proof's intermediate reductions.

Hypothesis and clause comparison:

| Node text | Lean rendering |
| --- | --- |
| S is any scheme | `(S : Scheme.{u})`, with no additional instance or hypothesis |
| T is an S-group scheme with multiplication, identity, inverse and group diagrams | `(T : Over S) [GrpObj T]` |
| T is a relative torus, fppf locally a finite power of G_m, with variable ranks | `(hT : IsRelativeTorus T)` uses the recorded definition verbatim |
| Set-indexed family U_j → S | `∃ (J : Type u) (U : J → Over S)` |
| Each map is étale | `∀ j : J, Etale (U j).hom` |
| Jointly covering images | `∀ s : S, ∃ (j : J) (x : (U j).left), (U j).hom x = s` |
| Finite-rank free abelian groups M_j | `M : J → AddCommGrpCat.{u}`, and `∀ j, Module.Free ℤ (M j) ∧ Module.Finite ℤ (M j)` |
| T ×_S U_j with its pulled-back group structure | `(Over.pullback (U j).hom).mapGrp.obj (Grp.mk T)` |
| D_(U_j)(M_j) | `(Over.pullback (U j).left.toSpecΓ).mapGrp.obj (ringDiagonalizableGroup Γ((U j).left, ⊤) (M j))` |
| Isomorphism as U_j-group schemes | `Nonempty (… ≅ …)` in `Grp (Over (U j).left)` |
| No finiteness, connectedness, normality, Noetherianity or henselianity of S | None of these appear as binders or hypotheses |
| Empty base and rank zero allowed | No `Nonempty J`, `Nonempty S` or positive-rank constraint |

The expression for D_U(M) is an actual canonical scheme construction using the
existing ring diagonalizable group. Write A = Γ(U,O_U). Pull back D_A(M) along
the canonical morphism U → Spec A. Its restriction to any affine open Spec C
is Spec(C ⊗_A A[M]) = Spec C[M]. The basis elements, coproduct, counit and
antipode are preserved by this scalar extension. The identifications use
restriction of global functions and agree on overlaps. Thus this is precisely
the group's gluing construction in the node, not an abstract group, an arbitrary
map, a representability assumption or a chosen object from mere existence.
The same tensor argument works for nonreduced rings and the zero ring.
No extra helper declaration is necessary.

Dependency declarations and sources read:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`, lines 35–48 and 73–76.
- `def-pc-fppf-site`: `Scheme.fppfPrecoverage` and `Scheme.fppfTopology`,
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`, lines 37–54. The hypothesis uses these
  through the actual recorded `IsRelativeTorus`, rather than a second cover predicate.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, lines 37–44. Its complete signature
  and affine-local ring-map condition were read. The stale search-service name
  `IsEtale` is a deprecated alias, not a reason to redefine the notion.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd` and `pullback.lift`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, lines 95–131.
  `Over.pullback` supplies exactly these products, and its `mapGrp` carries
  the multiplication, identity and inverse using finite-product preservation.
- `def-sfb-ring-diagonalizable-group`: `AlgebraicGeometry.ringDiagonalizableGroup`
  and `ringDiagonalizableGroupMap`, `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`.
  Read the entire file: the former is the Hopf spectrum of `AddMonoidAlgebra R M`
  with the existing monoid-algebra Hopf structure; it has no field or finiteness binder.
- `def-sfb-relative-torus`: `AlgebraicGeometry.relativeSplitTorusFunctor` and
  `AlgebraicGeometry.IsRelativeTorus`, `Sheaf.AlgebraicGeometry.RelativeTorus`.
  Read the entire file. `IsRelativeTorus` quantifies a `Type u` cover, its varying
  natural-number ranks, actual membership in `Scheme.fppfPrecoverage S`, and
  group-valued natural isomorphisms to the finite units functor. Its rank-zero
  functor is the empty product, hence the trivial group.

Additional existing interfaces used: `Scheme.toSpecΓ` is the unit of the
Gamma–Spec adjunction, `Mathlib.AlgebraicGeometry.GammaSpecAdjunction:434–436`;
`Functor.mapGrp`, `Mathlib.CategoryTheory.Monoidal.Grp:606–615`, transports
actual group objects along finite-product-preserving functors; the monoidal
pullback interface is `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`.
`Module.Free` is the existence of a basis (`FreeModule.Basic:42–44`) and
`Module.Finite` is finite generation, so their conjunction over ℤ says exactly
finite-rank free abelian, without choosing a basis as extra conclusion data.

Proof imports include the recorded modules of
`lem-sfb-scheme-etale-source-target-properties`, `def-trf-algebraic-space`,
and `lem-galois-fpqc-descend-etale`, and Mathlib's scheme gluing and coproduct
modules for the corresponding Mathlib leaves. The affine adjunction, fppf
base-change and fppf-to-fpqc leaves are already imported by statement imports.
The independent nodes `lem-sfb-relative-diagonalizable-character-duality` and
`lem-sfb-fppf-space-atlas-bootstrap` do not yet have recorded Lean modules,
so no imports can be added for them at this stage. `def-weil-size-convention`
is implemented by the shared universe u; its unrelated audit example of a
pro-étale derived category is not a declaration of this size convention and
is not imported as a purported proof dependency.

Edge cases checked before writing:

- Empty S: choose `J = PEmpty`; all covering and memberwise clauses are vacuous.
- Rank zero: M can be the zero abelian group; it is free and finitely generated,
  and A[0] = A, so D_U(0) is the terminal U-group scheme.
- Varying rank and infinitely many cover members: M depends on j, and J is not
  assumed finite. No connectedness or global-rank condition is imposed.
- Arbitrary nonaffine, nonnormal, non-Noetherian and nonreduced bases: the canonical
  pullback construction exists for each such U, and the cover's members need not
  be affine. No stronger hypothesis or affine-cover conclusion was inserted.
- Universes: all schemes, cover indices and lattice carriers use u, as in the
  recorded relative-torus definition. Finite free lattices admit this size;
  no independent smaller test-scheme universe makes the hypothesis vacuous.

Searches actually executed for an existing statement:

1. `msearch.py ... leanfinder "An fppf locally split torus over an arbitrary scheme is split on an etale covering"`:
   eight hits about étale morphisms, their category, topology and algebra properties;
   no torus-splitting statement.
2. `msearch.py ... loogle "AlgebraicGeometry.IsRelativeTorus, diagonalizable, IsEtale"`:
   zero hits; service reported unknown identifier `AlgebraicGeometry.IsRelativeTorus`.
3. `msearch.py ... grep "IsTorus|IsRelativeTorus|diagonalizable|Diagonalizable" AlgebraicGeometry`:
   zero Mathlib hits.
4. `msearch.py ... leansearch "A relative torus over any scheme splits on an etale covering as a diagonalizable group of a finite free abelian group"`:
   eight hits about étale sites and ring maps, and the unrelated analytic `UnitAddTorus`;
   no match.
5. `rg` in `lean/WeilConjectures` for relative tori, diagonalizable groups and étale
   splitting, and `grep -rn "lem-sfb-torus-etale-trivialization"` there: no match.
6. `rg` in `lean/Sheaf/AlgebraicGeometry` for `IsRelativeTorus`, diagonalizable groups
   and torus/étale statements: found the exact recorded relative-torus and ring-group
   definitions used here. `normal_torus_finite_etale_splitting` requires affine,
   normal and Noetherian S, so is not this arbitrary-base theorem. The field-only
   `diagonalizableGroup` is not used instead of `ringDiagonalizableGroup`.
7. `rg` for `relativeDiagonalizable`, `schemeDiagonalizable`, and related relative
   diagonalizable names across `lean/Sheaf`, `lean/WeilConjectures` and
   `dag/lean_names_upstream.json`: no existing general-base construction by these names.
   No definition was introduced: the canonical construction is written in the signature.
8. Exact-name search for `torus_etale_trivialization` across Mathlib, both project
   source trees and the upstream-name table: no collision.

No statement dispute or mathematical node fault was found. The only postponed
proof is `AlgebraicGeometry.torus_etale_trivialization`.

Validation: prescribed `scompile.py Q155 lem-sfb-torus-etale-trivialization <file>`
passed in both sandbox and actual module modes (16.9 s and 3.8 s respectively)
with no reported errors or non-sorry warnings. Final preflight and recompilation
are run again by the prescribed delivery wrapper.

## Second reading by Q155

This is the assigned worker's second consistency pass, not a claim of review by
another agent. The dispatch brief prohibits starting other agents and states
that the maintainer independently reviews this delivery.

Reopened the node and signature. Checked separately the sole structural binders
S, T and its group object, and the hypothesis `IsRelativeTorus T`. Reopened that
definition: its existing fppf cover and finite varying ranks are preserved.
Checked each of the four conclusion parts: étaleness, pointwise joint coverage,
finite free lattice, and isomorphism of the pulled-back group objects. In
particular the last clause uses `mapGrp` on both sides, rather than an isomorphism
of schemes forgetting the group law. The canonical pullback expression for D
recovers the specified affine group algebra on every affine chart, so it does
not substitute the arbitrary-base torus predicate for the conclusion.

Checked the empty and zero-rank cases again: neither J nor S has a nonemptiness
binder, and neither M nor its rank has a nonzero condition. Checked that no
finite cover, affine member, fixed rank or base regularity slipped into the
signature. The node copy differs only in `lean`; its recorded signature was
extracted verbatim from the final theorem keyword up to `:=`.
No mathematical mismatch was found. The second pass added explicit public
imports of the dependency modules and removed one stray space in the proof
docstring; it changed no statement.
