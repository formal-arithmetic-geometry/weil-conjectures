## Worker report

States `AlgebraicGeometry.relative_torus_monomorphism_closed` in
`Sheaf.AlgebraicGeometry.RelativeTorusMonomorphismClosed`. The only theorem has
proof `sorry`; no definition, axiom, helper theorem or proof is introduced.
The module docstring and theorem docstring identify Conrad, Reductive group
schemes, Theorem 5.3.5, printed pp.165–168, and Appendix B Lemma B.1.3,
pp.281–282, with Prasad–Yu Proposition 3.1 for the nonaffine reduction. The
latter theorem specializes from reductive groups to tori. I opened Conrad's
PDF online and read the statement and direct-limit/DVR/schematic-closure
reduction on pp.165–166. The ten proof steps in the accepted node are rendered
in the theorem docstring, including their supporting node identifiers.

The previous worker's failure concerned stage-1 splitting. The current node
is `split`, reviewed pass for N5 on 2026-10-24, has no Lean record, and appears
as stage 2 in coord/queue.tsv. The stage handoff at brief-stage2 §0 explicitly
permits this stage-2 statement without reopening the accepted split.

Clause-by-clause match:

| Node clause | Lean |
| --- | --- |
| Any scheme S | `{S : Scheme.{u}}`, with explicit `universe u` and no field, nonempty or Noetherian assumption |
| P and G are S-schemes | `(P G : Over S)`; their structure maps are `P.hom` and `G.hom` |
| Multiplication, identity, inverse and group diagrams on each | `[GrpObj P] [GrpObj G]`, group objects in the cartesian monoidal category `Over S` |
| P commutative | `[IsCommMonObj P]` uses the same underlying monoid structure as `GrpObj P` |
| P smooth | `[Smooth P.hom]` |
| P affine over S | `[IsAffineHom P.hom]`; this does not require P or S absolutely affine |
| P of finite presentation | `[LocallyOfFinitePresentation P.hom] [QuasiCompact P.hom] [QuasiSeparated P.hom]`, the three conditions fixed by def-weil-pbc-scheme-conventions |
| P fppf locally G_m to a finite locally constant rank, allowing zero | `(hP : IsRelativeTorus P)` using the already landed relative-torus definition, with finite ranks allowed to vary across cover members |
| G separated over S | `[IsSeparated G.hom]` |
| G of finite presentation | `[LocallyOfFinitePresentation G.hom] [QuasiCompact G.hom] [QuasiSeparated G.hom]` |
| u an S-group homomorphism | `(u : P ⟶ G) [IsMonHom u]`; membership in `Over S` gives the structural commutative triangle, and a monoid homomorphism between group objects preserves inverse |
| All S-schemes T and injectivity of P(T) to G(T) | `(hu : ∀ (T : Over S), Function.Injective (fun x : T ⟶ P => x ≫ u))`; these hom sets are precisely Hom_S(T,P) and Hom_S(T,G) |
| u closed immersion | `IsClosedImmersion u.left` on the underlying scheme morphism |

No hypothesis on flatness, smoothness, commutativity or affineness of G was
added. No assumption on u beyond being an S-group homomorphism and injectivity
on all S-scheme points was added. All variables and universes are explicit;
`autoImplicit` and `relaxedAutoImplicit` are both false. No `let`, `show`, local
notation, private definition or file-local instance occurs in the statement.

Dependencies read and used:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Scheme` and its category of morphisms.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth,
  `AlgebraicGeometry.Smooth`.
- def-weil-pbc-scheme-conventions is explicitly a convention node with no
  declaration. Its finite-presentation convention is rendered by the three
  Mathlib classes above; separatedness and affineness use `IsSeparated` and
  `IsAffineHom`, whose source signatures were inspected.
- def-pc-fppf-site: Mathlib.AlgebraicGeometry.Sites.Fpqc,
  `AlgebraicGeometry.Scheme.fppfPrecoverage` and `fppfTopology`. The actual
  fppf precoverage appears inside the reused `IsRelativeTorus` definition.
- def-sc-gm-ga: read `StandardGroupSchemes.multiplicative` and its group-law
  declaration/docstrings in Sheaf.AlgebraicGeometry.StandardGroupSchemes.
  That node and its signature require a FIELD and therefore do not define
  the relative multiplicative group over the arbitrary base of this item.
  No field-only specialization or private replacement is used. Instead the
  already landed def-sfb-relative-torus supplies the exact relative group
  functor and local splitting condition. Its definition, source, full signature
  and accepted review were read. The old field-only dependency remains
  untouched, and def-sfb-relative-torus is added to stmt_deps, as authorized
  for already landed notions by brief-stage2 §5. This needs no new node or
  dependency repair, and changes no mathematical statement.
- def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  `AlgebraicGeometry.IsClosedImmersion`, the closed embedding with surjective
  maps on stalks.
- def-sfb-relative-torus: Sheaf.AlgebraicGeometry.RelativeTorus,
  `AlgebraicGeometry.IsRelativeTorus` and `relativeSplitTorusFunctor`.
  The functor assigns finite products of units of global functions, including
  the terminal group at rank zero, and its isomorphisms are group-valued.

The modules of already stated proof dependencies are imported with ordinary
`import`: Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent
(`isClosedImmersion_of_fpqc_cover`),
WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
(`Scheme.NoetherianApproximation.ofIsAffine`,
`Scheme.exists_pullback_hom_of_isLimit`,
`Scheme.exists_pullback_fst_comp_eq_of_isLimit`),
WeilConjectures.AlgebraicGeometry.ExistsIsSeparatedOverPullbackMap
(`Scheme.exists_isSeparated_overPullbackMap`),
WeilConjectures.AlgebraicGeometry.DescendMonomorphism
(`exists_mono_baseChange_stage`),
Sheaf.AlgebraicGeometry.NoetherianDvrProperness
(`isProper_iff_unique_dvr_lift`), and
Mathlib.AlgebraicGeometry.ZariskisMainTheorem
(`IsClosedImmersion.iff_isProper_and_mono`).
The remaining Mathlib proof leaves use Precoverage, Sites.Fpqc, Noetherian,
Smooth and ClosedImmersion, all imported directly or through statement
imports. Not-yet-stated proof-only nodes have no modules to import:
algebraic-group-monomorphism-closed-immersion, dvr-flat-generic-subgroup-closure,
relative-torus-character-reconstruction, dvr-generic-affine-group-affine and
affine-multiplicative-type-monomorphism-closed (each with prefix lem-sfb-).
They are named in the ten-step docstring rather than replaced or asserted.

Edge cases checked before writing: the empty base is admitted (no Nonempty
binder and the relative-torus definition permits an empty cover); rank zero
is the trivial group and u is its identity section in a separated group,
which is closed; ranks may differ on components or splitting members; bases
may be nonreduced and non-Noetherian; G may be nonaffine, nonflat,
noncommutative or nonsmooth. Injectivity tests every S-scheme, including
nonreduced test schemes: it is not restricted to field-valued or geometric
points (so e.g. a characteristic-p power map with nontrivial infinitesimal
kernel cannot pass the injectivity assumption). Target quasi-compactness is
retained: Conrad explicitly warns that only locally finite presentation is
insufficient. A separate universe for test schemes is not introduced; all
schemes range over the common size universe of Scheme.{u}.

Searches (msearch.py, group NR and this item; all on 2026-10-24):

- leanfinder: "A monomorphism from a torus over a scheme to a separated group
  scheme of finite presentation is a closed immersion". Eight results,
  including closed diagonals and `IsClosedImmersion.iff_isFinite_and_mono`;
  none states this torus theorem.
- loogle: `"AlgebraicGeometry", "Mono", "IsClosedImmersion"`. Four results:
  finite/proper monomorphism characterizations and their property equalities.
  They need properness or finiteness, the substance of the present theorem.
- grep: `Torus|IsTorus|torus` in Mathlib/AlgebraicGeometry. Zero hits.
- leansearch: "A monic relative torus homomorphism into a separated finitely
  presented group scheme is a closed immersion". Eight results on closed
  immersions and their characterizations, none the target theorem.
- rg in lean/WeilConjectures and lean/Sheaf for group schemes, relative tori,
  IsRelativeTorus and the desired theorem's names; grep -rn for the item id
  in lean/WeilConjectures. No existing theorem; found and reused the landed
  RelativeTorus definition rather than inventing another torus.
- DAG search found def-sfb-relative-torus with an accepted Lean record and
  no competing declaration for the target theorem.

No STATEMENT-DISPUTED issue or statement correction is needed. The item's
statement and accepted split are unchanged. Only lean and the addition of
the already landed relative-torus dependency change.

Validation: scompile.py compiled the sandbox and exact library module cleanly
(4.5 s and 4.1 s); there is only the expected sorry proof. An initial unknown
`CommGrpObj` was repaired by using `GrpObj` with `IsCommMonObj` and importing
the owning Mathlib commutative-monoid-object module. There is one consistent
underlying group-object structure on P.

## Second reading by NR

The dispatcher forbids starting another agent, so this is a separate reread
by the same worker, not a claim of independent review; the maintainer's
independent review remains required. I reopened the complete node statement,
the relative-torus definition, and the final theorem signature. S is arbitrary;
P has precisely its group, commutativity, smooth, affine, finite-presentation
and local-splitting data; G has group, separatedness and finite-presentation
data; u is an S-group homomorphism; `hu` quantifies over all Over S objects;
the conclusion concerns the underlying u.left. Each clause matches the table
above. The inherited field-only G_m citation cannot supply a relative object,
so the already landed relative-torus dependency is cited explicitly. No
weaker pointwise condition, global constant-rank requirement or affineness
hypothesis on G appears. Removed the redundant second group-object structure
from the initial draft by using `IsCommMonObj P` alongside `GrpObj P`.
