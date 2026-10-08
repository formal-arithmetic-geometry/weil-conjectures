+++
id = "sbc-def-base-change-map"
kind = "definition"
title = "Base-change map"
order = 1367
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-derived-exchange", "def-weil-pbc-direct-image", "def-weil-pbc-inverse-image", "def-weil-pbc-kinjective-resolutions", "sbc-def-base-change-square"]
+++
For a base-change square and
$K\in D(T_{\Et},\Lambda)$, the *derived base-change map* is the
morphism

$$
{\operatorname{BC}}_{f,g}(K):Lf^*Rg_*K
\longrightarrow Rh_*Le^*K
$$

of $D(X_{\Et},\Lambda)$ defined as the composite

$$
\begin{array}{l}
Lf^*Rg_*K\xrightarrow{\;\eta_e\;}
Lf^*Rg_*Re_*Le^*K
\;\cong\;Lf^*R(ge)_*Le^*K
\;\cong\;Lf^*Rf_*Rh_*Le^*K\\
\hphantom{Lf^*Rg_*K\xrightarrow{\;\eta_e\;}}
\xrightarrow{\;\varepsilon_f\;}
Rh_*Le^*K,
\end{array}
$$

where $\eta_e$ is the unit of the adjunction
$Le^*\dashv Re_*$, where $ge=fh$ gives the two canonical
identifications of the composite functors, and where
$\varepsilon_f$ is the counit of $Lf^*\dashv Rf_*$; it is
the derived exchange morphism of
[def-weil-pbc-derived-exchange] read on the same
square with the vertical and horizontal sides exchanged. Its
naturality in $K$ is the corresponding statement below, and its
compatibility with the composition of squares and with base change
along the square is the corresponding statement below and
the corresponding statement below.
For $F\in\Ab(T_{\Et})$, the *base-change map in degree $q$* is
the $q$-th cohomology sheaf of $\operatorname{BC}_{f,g}$ applied to
$F$ (placed in degree zero):

$$
{\operatorname{BC}}^q_{f,g}(F):=H^q\bigl(\operatorname{BC}_{f,g}(F)\bigr)
:f^{-1}R^qg_*F
\longrightarrow R^qh_*e^{-1}F,
$$

the identifications of the two sides following from the exactness of
$f^{-1}$ and of $e^{-1}$ on sheaves and from the definitions of the
higher direct images of
[def-weil-pbc-direct-image]; in degree $q=0$ this is the
sheaf-level base-change map obtained by the composition

$$
h^{-1}f^{-1}g_*F\xrightarrow{\theta_\square}
e^{-1}g^{-1}g_*F\xrightarrow{e^{-1}\varepsilon_g}e^{-1}F
$$

(valid for $q=0$ because the counit
$\varepsilon_g:g^{-1}g_*\to\operatorname{id}$ is a morphism of
functors on sheaves on $T_{\Et}$), transposed under
$h^{-1}\dashv h_*$.
