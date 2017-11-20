%------------------------------------------------------------------------------
% File     : NUM923^1 : TPTP v7.0.0. Released v5.3.0.
% Domain   : Number Theory
% Problem  : Sum of two squares line 23, 100 axioms selected
% Version  : Especial.
% English  :

% Refs     : [BN10]  Boehme & Nipkow (2010), Sledgehammer: Judgement Day
%          : [Bla11] Blanchette (2011), Email to Geoff Sutcliffe
% Source   : [Bla11]
% Names    : s2s_100_thf_l23 [Bla11]

% Status   : Theorem
% Rating   : 1.00 v5.3.0
% Syntax   : Number of formulae    :   91 (   0 unit;  16 type;   0 defn)
%            Number of atoms       :  874 (  72 equality; 486 variable)
%            Maximal formula depth :   16 (   8 average)
%            Number of connectives :  665 (  10   ~;   2   |;   2   &; 611   @)
%                                         (  17 <=>;  23  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :   26 (  26   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   18 (  16   :;   0   =)
%            Number of variables   :  235 (   0 sgn; 231   !;   4   ?;   0   ^)
%                                         ( 235   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU_NAR

% Comments : This file was generated by Isabelle (most likely Sledgehammer)
%            2011-08-09 19:02:52
%------------------------------------------------------------------------------
%----Should-be-implicit typings (2)
thf(ty_ty_tc__Int__Oint,type,(
    int: $tType )).

thf(ty_ty_tc__prod_Itc__Int__Oint_Mtc__Int__Oint_J,type,(
    product_prod_int_int: $tType )).

%----Explicit typings (14)
thf(sy_c_All,type,(
    all: ( product_prod_int_int > $o ) > $o )).

thf(sy_c_Ex,type,(
    ex: ( product_prod_int_int > $o ) > $o )).

thf(sy_c_Groups_Ominus__class_Ominus_000tc__Int__Oint,type,(
    minus_minus_int: int > int > int )).

thf(sy_c_Groups_Oplus__class_Oplus_000tc__Int__Oint,type,(
    plus_plus_int: int > int > int )).

thf(sy_c_Groups_Otimes__class_Otimes_000tc__Int__Oint,type,(
    times_times_int: int > int > int )).

thf(sy_c_Orderings_Oord__class_Oless__eq_000tc__Int__Oint,type,(
    ord_less_eq_int: int > int > $o )).

thf(sy_c_Product__Type_OPair_000tc__Int__Oint_000tc__Int__Oint,type,(
    product_Pair_int_int: int > int > product_prod_int_int )).

thf(sy_c_Product__Type_Ocurry_000tc__Int__Oint_000tc__Int__Oint_000_Eo,type,(
    produc176579150_int_o: ( product_prod_int_int > $o ) > int > int > $o )).

thf(sy_c_TwoSquares__Mirabelle__fqdbopfjxb_Ois__sum2sq,type,(
    twoSqu1013291560sum2sq: int > $o )).

thf(sy_c_TwoSquares__Mirabelle__fqdbopfjxb_Osum2sq,type,(
    twoSqu1535104286sum2sq: product_prod_int_int > int )).

thf(sy_v_a,type,(
    a: int )).

thf(sy_v_b,type,(
    b: int )).

thf(sy_v_p,type,(
    p: int )).

thf(sy_v_q,type,(
    q: int )).

%----Relevant facts (74)
thf(fact_0_xzgcda__linear__aux1,axiom,(
    ! [A_42: int,R: int,B_39: int,M_1: int,C_29: int,D_12: int,N: int] :
      ( ( plus_plus_int @ ( times_times_int @ ( minus_minus_int @ A_42 @ ( times_times_int @ R @ B_39 ) ) @ M_1 ) @ ( times_times_int @ ( minus_minus_int @ C_29 @ ( times_times_int @ R @ D_12 ) ) @ N ) )
      = ( minus_minus_int @ ( plus_plus_int @ ( times_times_int @ A_42 @ M_1 ) @ ( times_times_int @ C_29 @ N ) ) @ ( times_times_int @ R @ ( plus_plus_int @ ( times_times_int @ B_39 @ M_1 ) @ ( times_times_int @ D_12 @ N ) ) ) ) ) )).

thf(fact_1_mult__diff__mult,axiom,(
    ! [X_6: int,Y_6: int,A_45: int,B_42: int] :
      ( ( minus_minus_int @ ( times_times_int @ X_6 @ Y_6 ) @ ( times_times_int @ A_45 @ B_42 ) )
      = ( plus_plus_int @ ( times_times_int @ X_6 @ ( minus_minus_int @ Y_6 @ B_42 ) ) @ ( times_times_int @ ( minus_minus_int @ X_6 @ A_45 ) @ B_42 ) ) ) )).

thf(fact_2_eq__add__iff2,axiom,(
    ! [A_44: int,E_4: int,C_31: int,B_41: int,D_11: int] :
      ( ( ( plus_plus_int @ ( times_times_int @ A_44 @ E_4 ) @ C_31 )
        = ( plus_plus_int @ ( times_times_int @ B_41 @ E_4 ) @ D_11 ) )
    <=> ( C_31
        = ( plus_plus_int @ ( times_times_int @ ( minus_minus_int @ B_41 @ A_44 ) @ E_4 ) @ D_11 ) ) ) )).

thf(fact_3_eq__add__iff1,axiom,(
    ! [A_43: int,E_3: int,C_30: int,B_40: int,D_10: int] :
      ( ( ( plus_plus_int @ ( times_times_int @ A_43 @ E_3 ) @ C_30 )
        = ( plus_plus_int @ ( times_times_int @ B_40 @ E_3 ) @ D_10 ) )
    <=> ( ( plus_plus_int @ ( times_times_int @ ( minus_minus_int @ A_43 @ B_40 ) @ E_3 ) @ C_30 )
        = D_10 ) ) )).

thf(fact_4_is__sum2sq__def,axiom,(
    ! [X_5: int] :
      ( ( twoSqu1013291560sum2sq @ X_5 )
    <=> ? [A_14: int,B_14: int] :
          ( ( twoSqu1535104286sum2sq @ ( product_Pair_int_int @ A_14 @ B_14 ) )
          = X_5 ) ) )).

thf(fact_5_Int2_Oaux1,axiom,(
    ! [A_42: int,B_39: int,C_29: int] :
      ( ( ( minus_minus_int @ A_42 @ B_39 )
        = C_29 )
     => ( A_42
        = ( plus_plus_int @ C_29 @ B_39 ) ) ) )).

thf(fact_6_zdiff__zmult__distrib2,axiom,(
    ! [W: int,Z1: int,Z2: int] :
      ( ( times_times_int @ W @ ( minus_minus_int @ Z1 @ Z2 ) )
      = ( minus_minus_int @ ( times_times_int @ W @ Z1 ) @ ( times_times_int @ W @ Z2 ) ) ) )).

thf(fact_7_zdiff__zmult__distrib,axiom,(
    ! [Z1: int,Z2: int,W: int] :
      ( ( times_times_int @ ( minus_minus_int @ Z1 @ Z2 ) @ W )
      = ( minus_minus_int @ ( times_times_int @ Z1 @ W ) @ ( times_times_int @ Z2 @ W ) ) ) )).

thf(fact_8_zadd__zmult__distrib2,axiom,(
    ! [W: int,Z1: int,Z2: int] :
      ( ( times_times_int @ W @ ( plus_plus_int @ Z1 @ Z2 ) )
      = ( plus_plus_int @ ( times_times_int @ W @ Z1 ) @ ( times_times_int @ W @ Z2 ) ) ) )).

thf(fact_9_zadd__zmult__distrib,axiom,(
    ! [Z1: int,Z2: int,W: int] :
      ( ( times_times_int @ ( plus_plus_int @ Z1 @ Z2 ) @ W )
      = ( plus_plus_int @ ( times_times_int @ Z1 @ W ) @ ( times_times_int @ Z2 @ W ) ) ) )).

thf(fact_10_diff__add__cancel,axiom,(
    ! [A_41: int,B_38: int] :
      ( ( plus_plus_int @ ( minus_minus_int @ A_41 @ B_38 ) @ B_38 )
      = A_41 ) )).

thf(fact_11_ab__semigroup__mult__class_Omult__ac_I1_J,axiom,(
    ! [A_40: int,B_37: int,C_28: int] :
      ( ( times_times_int @ ( times_times_int @ A_40 @ B_37 ) @ C_28 )
      = ( times_times_int @ A_40 @ ( times_times_int @ B_37 @ C_28 ) ) ) )).

thf(fact_12_add__right__imp__eq,axiom,(
    ! [B_36: int,A_39: int,C_27: int] :
      ( ( ( plus_plus_int @ B_36 @ A_39 )
        = ( plus_plus_int @ C_27 @ A_39 ) )
     => ( B_36 = C_27 ) ) )).

thf(fact_13_add__imp__eq,axiom,(
    ! [A_38: int,B_35: int,C_26: int] :
      ( ( ( plus_plus_int @ A_38 @ B_35 )
        = ( plus_plus_int @ A_38 @ C_26 ) )
     => ( B_35 = C_26 ) ) )).

thf(fact_14_add__left__imp__eq,axiom,(
    ! [A_37: int,B_34: int,C_25: int] :
      ( ( ( plus_plus_int @ A_37 @ B_34 )
        = ( plus_plus_int @ A_37 @ C_25 ) )
     => ( B_34 = C_25 ) ) )).

thf(fact_15_add__right__cancel,axiom,(
    ! [B_33: int,A_36: int,C_24: int] :
      ( ( ( plus_plus_int @ B_33 @ A_36 )
        = ( plus_plus_int @ C_24 @ A_36 ) )
    <=> ( B_33 = C_24 ) ) )).

thf(fact_16_add__left__cancel,axiom,(
    ! [A_35: int,B_32: int,C_23: int] :
      ( ( ( plus_plus_int @ A_35 @ B_32 )
        = ( plus_plus_int @ A_35 @ C_23 ) )
    <=> ( B_32 = C_23 ) ) )).

thf(fact_17_ab__semigroup__add__class_Oadd__ac_I1_J,axiom,(
    ! [A_34: int,B_31: int,C_22: int] :
      ( ( plus_plus_int @ ( plus_plus_int @ A_34 @ B_31 ) @ C_22 )
      = ( plus_plus_int @ A_34 @ ( plus_plus_int @ B_31 @ C_22 ) ) ) )).

thf(fact_18_diff__eq__diff__eq,axiom,(
    ! [A_33: int,B_30: int,C_21: int,D_9: int] :
      ( ( ( minus_minus_int @ A_33 @ B_30 )
        = ( minus_minus_int @ C_21 @ D_9 ) )
     => ( ( A_33 = B_30 )
      <=> ( C_21 = D_9 ) ) ) )).

thf(fact_19_zmult__assoc,axiom,(
    ! [Z1: int,Z2: int,Z3: int] :
      ( ( times_times_int @ ( times_times_int @ Z1 @ Z2 ) @ Z3 )
      = ( times_times_int @ Z1 @ ( times_times_int @ Z2 @ Z3 ) ) ) )).

thf(fact_20_zmult__commute,axiom,(
    ! [Z: int,W: int] :
      ( ( times_times_int @ Z @ W )
      = ( times_times_int @ W @ Z ) ) )).

thf(fact_21_zadd__assoc,axiom,(
    ! [Z1: int,Z2: int,Z3: int] :
      ( ( plus_plus_int @ ( plus_plus_int @ Z1 @ Z2 ) @ Z3 )
      = ( plus_plus_int @ Z1 @ ( plus_plus_int @ Z2 @ Z3 ) ) ) )).

thf(fact_22_zadd__left__commute,axiom,(
    ! [X_5: int,Y_5: int,Z: int] :
      ( ( plus_plus_int @ X_5 @ ( plus_plus_int @ Y_5 @ Z ) )
      = ( plus_plus_int @ Y_5 @ ( plus_plus_int @ X_5 @ Z ) ) ) )).

thf(fact_23_zadd__commute,axiom,(
    ! [Z: int,W: int] :
      ( ( plus_plus_int @ Z @ W )
      = ( plus_plus_int @ W @ Z ) ) )).

thf(fact_24_combine__common__factor,axiom,(
    ! [A_32: int,E_2: int,B_29: int,C_20: int] :
      ( ( plus_plus_int @ ( times_times_int @ A_32 @ E_2 ) @ ( plus_plus_int @ ( times_times_int @ B_29 @ E_2 ) @ C_20 ) )
      = ( plus_plus_int @ ( times_times_int @ ( plus_plus_int @ A_32 @ B_29 ) @ E_2 ) @ C_20 ) ) )).

thf(fact_25_comm__semiring__class_Odistrib,axiom,(
    ! [A_31: int,B_28: int,C_19: int] :
      ( ( times_times_int @ ( plus_plus_int @ A_31 @ B_28 ) @ C_19 )
      = ( plus_plus_int @ ( times_times_int @ A_31 @ C_19 ) @ ( times_times_int @ B_28 @ C_19 ) ) ) )).

thf(fact_26_add__diff__add,axiom,(
    ! [A_30: int,C_18: int,B_27: int,D_8: int] :
      ( ( minus_minus_int @ ( plus_plus_int @ A_30 @ C_18 ) @ ( plus_plus_int @ B_27 @ D_8 ) )
      = ( plus_plus_int @ ( minus_minus_int @ A_30 @ B_27 ) @ ( minus_minus_int @ C_18 @ D_8 ) ) ) )).

thf(fact_27_add__diff__cancel,axiom,(
    ! [A_29: int,B_26: int] :
      ( ( minus_minus_int @ ( plus_plus_int @ A_29 @ B_26 ) @ B_26 )
      = A_29 ) )).

thf(fact_28_crossproduct__eq,axiom,(
    ! [W_1: int,Y_4: int,X_4: int,Z_2: int] :
      ( ( ( plus_plus_int @ ( times_times_int @ W_1 @ Y_4 ) @ ( times_times_int @ X_4 @ Z_2 ) )
        = ( plus_plus_int @ ( times_times_int @ W_1 @ Z_2 ) @ ( times_times_int @ X_4 @ Y_4 ) ) )
    <=> ( ( W_1 = X_4 )
        | ( Y_4 = Z_2 ) ) ) )).

thf(fact_29_comm__semiring__1__class_Onormalizing__semiring__rules_I1_J,axiom,(
    ! [A_28: int,M: int,B_25: int] :
      ( ( plus_plus_int @ ( times_times_int @ A_28 @ M ) @ ( times_times_int @ B_25 @ M ) )
      = ( times_times_int @ ( plus_plus_int @ A_28 @ B_25 ) @ M ) ) )).

thf(fact_30_comm__semiring__1__class_Onormalizing__semiring__rules_I8_J,axiom,(
    ! [A_27: int,B_24: int,C_17: int] :
      ( ( times_times_int @ ( plus_plus_int @ A_27 @ B_24 ) @ C_17 )
      = ( plus_plus_int @ ( times_times_int @ A_27 @ C_17 ) @ ( times_times_int @ B_24 @ C_17 ) ) ) )).

thf(fact_31_crossproduct__noteq,axiom,(
    ! [C_16: int,D_7: int,A_26: int,B_23: int] :
      ( ( ( A_26 != B_23 )
        & ( C_16 != D_7 ) )
    <=> ( ( plus_plus_int @ ( times_times_int @ A_26 @ C_16 ) @ ( times_times_int @ B_23 @ D_7 ) )
       != ( plus_plus_int @ ( times_times_int @ A_26 @ D_7 ) @ ( times_times_int @ B_23 @ C_16 ) ) ) ) )).

thf(fact_32_comm__semiring__1__class_Onormalizing__semiring__rules_I34_J,axiom,(
    ! [X_3: int,Y_3: int,Z_1: int] :
      ( ( times_times_int @ X_3 @ ( plus_plus_int @ Y_3 @ Z_1 ) )
      = ( plus_plus_int @ ( times_times_int @ X_3 @ Y_3 ) @ ( times_times_int @ X_3 @ Z_1 ) ) ) )).

thf(fact_33_Pair__inject,axiom,(
    ! [A_25: int,B_22: int,A_24: int,B_21: int] :
      ( ( ( product_Pair_int_int @ A_25 @ B_22 )
        = ( product_Pair_int_int @ A_24 @ B_21 ) )
     => ~ ( ( A_25 = A_24 )
         => ( B_22 != B_21 ) ) ) )).

thf(fact_34_Pair__eq,axiom,(
    ! [A_23: int,B_20: int,A_22: int,B_19: int] :
      ( ( ( product_Pair_int_int @ A_23 @ B_20 )
        = ( product_Pair_int_int @ A_22 @ B_19 ) )
    <=> ( ( A_23 = A_22 )
        & ( B_20 = B_19 ) ) ) )).

thf(fact_35_comm__semiring__1__class_Onormalizing__semiring__rules_I7_J,axiom,(
    ! [A_21: int,B_18: int] :
      ( ( times_times_int @ A_21 @ B_18 )
      = ( times_times_int @ B_18 @ A_21 ) ) )).

thf(fact_36_comm__semiring__1__class_Onormalizing__semiring__rules_I19_J,axiom,(
    ! [Lx_6: int,Rx_6: int,Ry_4: int] :
      ( ( times_times_int @ Lx_6 @ ( times_times_int @ Rx_6 @ Ry_4 ) )
      = ( times_times_int @ Rx_6 @ ( times_times_int @ Lx_6 @ Ry_4 ) ) ) )).

thf(fact_37_comm__semiring__1__class_Onormalizing__semiring__rules_I18_J,axiom,(
    ! [Lx_5: int,Rx_5: int,Ry_3: int] :
      ( ( times_times_int @ Lx_5 @ ( times_times_int @ Rx_5 @ Ry_3 ) )
      = ( times_times_int @ ( times_times_int @ Lx_5 @ Rx_5 ) @ Ry_3 ) ) )).

thf(fact_38_comm__semiring__1__class_Onormalizing__semiring__rules_I17_J,axiom,(
    ! [Lx_4: int,Ly_4: int,Rx_4: int] :
      ( ( times_times_int @ ( times_times_int @ Lx_4 @ Ly_4 ) @ Rx_4 )
      = ( times_times_int @ Lx_4 @ ( times_times_int @ Ly_4 @ Rx_4 ) ) ) )).

thf(fact_39_comm__semiring__1__class_Onormalizing__semiring__rules_I16_J,axiom,(
    ! [Lx_3: int,Ly_3: int,Rx_3: int] :
      ( ( times_times_int @ ( times_times_int @ Lx_3 @ Ly_3 ) @ Rx_3 )
      = ( times_times_int @ ( times_times_int @ Lx_3 @ Rx_3 ) @ Ly_3 ) ) )).

thf(fact_40_comm__semiring__1__class_Onormalizing__semiring__rules_I14_J,axiom,(
    ! [Lx_2: int,Ly_2: int,Rx_2: int,Ry_2: int] :
      ( ( times_times_int @ ( times_times_int @ Lx_2 @ Ly_2 ) @ ( times_times_int @ Rx_2 @ Ry_2 ) )
      = ( times_times_int @ Lx_2 @ ( times_times_int @ Ly_2 @ ( times_times_int @ Rx_2 @ Ry_2 ) ) ) ) )).

thf(fact_41_comm__semiring__1__class_Onormalizing__semiring__rules_I15_J,axiom,(
    ! [Lx_1: int,Ly_1: int,Rx_1: int,Ry_1: int] :
      ( ( times_times_int @ ( times_times_int @ Lx_1 @ Ly_1 ) @ ( times_times_int @ Rx_1 @ Ry_1 ) )
      = ( times_times_int @ Rx_1 @ ( times_times_int @ ( times_times_int @ Lx_1 @ Ly_1 ) @ Ry_1 ) ) ) )).

thf(fact_42_comm__semiring__1__class_Onormalizing__semiring__rules_I13_J,axiom,(
    ! [Lx: int,Ly: int,Rx: int,Ry: int] :
      ( ( times_times_int @ ( times_times_int @ Lx @ Ly ) @ ( times_times_int @ Rx @ Ry ) )
      = ( times_times_int @ ( times_times_int @ Lx @ Rx ) @ ( times_times_int @ Ly @ Ry ) ) ) )).

thf(fact_43_comm__semiring__1__class_Onormalizing__semiring__rules_I24_J,axiom,(
    ! [A_20: int,C_15: int] :
      ( ( plus_plus_int @ A_20 @ C_15 )
      = ( plus_plus_int @ C_15 @ A_20 ) ) )).

thf(fact_44_comm__semiring__1__class_Onormalizing__semiring__rules_I22_J,axiom,(
    ! [A_19: int,C_14: int,D_6: int] :
      ( ( plus_plus_int @ A_19 @ ( plus_plus_int @ C_14 @ D_6 ) )
      = ( plus_plus_int @ C_14 @ ( plus_plus_int @ A_19 @ D_6 ) ) ) )).

thf(fact_45_comm__semiring__1__class_Onormalizing__semiring__rules_I25_J,axiom,(
    ! [A_18: int,C_13: int,D_5: int] :
      ( ( plus_plus_int @ A_18 @ ( plus_plus_int @ C_13 @ D_5 ) )
      = ( plus_plus_int @ ( plus_plus_int @ A_18 @ C_13 ) @ D_5 ) ) )).

thf(fact_46_comm__semiring__1__class_Onormalizing__semiring__rules_I21_J,axiom,(
    ! [A_17: int,B_17: int,C_12: int] :
      ( ( plus_plus_int @ ( plus_plus_int @ A_17 @ B_17 ) @ C_12 )
      = ( plus_plus_int @ A_17 @ ( plus_plus_int @ B_17 @ C_12 ) ) ) )).

thf(fact_47_comm__semiring__1__class_Onormalizing__semiring__rules_I23_J,axiom,(
    ! [A_16: int,B_16: int,C_11: int] :
      ( ( plus_plus_int @ ( plus_plus_int @ A_16 @ B_16 ) @ C_11 )
      = ( plus_plus_int @ ( plus_plus_int @ A_16 @ C_11 ) @ B_16 ) ) )).

thf(fact_48_comm__semiring__1__class_Onormalizing__semiring__rules_I20_J,axiom,(
    ! [A_15: int,B_15: int,C_10: int,D_4: int] :
      ( ( plus_plus_int @ ( plus_plus_int @ A_15 @ B_15 ) @ ( plus_plus_int @ C_10 @ D_4 ) )
      = ( plus_plus_int @ ( plus_plus_int @ A_15 @ C_10 ) @ ( plus_plus_int @ B_15 @ D_4 ) ) ) )).

thf(fact_49_split__paired__All,axiom,(
    ! [P_2: product_prod_int_int > $o] :
      ( ( all @ P_2 )
    <=> ! [A_14: int,B_14: int] :
          ( P_2 @ ( product_Pair_int_int @ A_14 @ B_14 ) ) ) )).

thf(fact_50_split__paired__Ex,axiom,(
    ! [P_1: product_prod_int_int > $o] :
      ( ( ex @ P_1 )
    <=> ? [A_14: int,B_14: int] :
          ( P_1 @ ( product_Pair_int_int @ A_14 @ B_14 ) ) ) )).

thf(fact_51_prod_Oexhaust,axiom,(
    ! [Y_2: product_prod_int_int] :
      ~ ( ! [A_14: int,B_14: int] :
            ( Y_2
           != ( product_Pair_int_int @ A_14 @ B_14 ) ) ) )).

thf(fact_52_PairE,axiom,(
    ! [P: product_prod_int_int] :
      ~ ( ! [X_2: int,Y_1: int] :
            ( P
           != ( product_Pair_int_int @ X_2 @ Y_1 ) ) ) )).

thf(fact_53_curryI,axiom,(
    ! [F_3: product_prod_int_int > $o,A_13: int,B_13: int] :
      ( ( F_3 @ ( product_Pair_int_int @ A_13 @ B_13 ) )
     => ( produc176579150_int_o @ F_3 @ A_13 @ B_13 ) ) )).

thf(fact_54_curryD,axiom,(
    ! [F_2: product_prod_int_int > $o,A_12: int,B_12: int] :
      ( ( produc176579150_int_o @ F_2 @ A_12 @ B_12 )
     => ( F_2 @ ( product_Pair_int_int @ A_12 @ B_12 ) ) ) )).

thf(fact_55_curryE,axiom,(
    ! [F_1: product_prod_int_int > $o,A_11: int,B_11: int] :
      ( ( produc176579150_int_o @ F_1 @ A_11 @ B_11 )
     => ( F_1 @ ( product_Pair_int_int @ A_11 @ B_11 ) ) ) )).

thf(fact_56_curry__conv,axiom,(
    ! [F: product_prod_int_int > $o,A_10: int,B_10: int] :
      ( ( produc176579150_int_o @ F @ A_10 @ B_10 )
    <=> ( F @ ( product_Pair_int_int @ A_10 @ B_10 ) ) ) )).

thf(fact_57_le__add__iff1,axiom,(
    ! [A_9: int,E_1: int,C_9: int,B_9: int,D_3: int] :
      ( ( ord_less_eq_int @ ( plus_plus_int @ ( times_times_int @ A_9 @ E_1 ) @ C_9 ) @ ( plus_plus_int @ ( times_times_int @ B_9 @ E_1 ) @ D_3 ) )
    <=> ( ord_less_eq_int @ ( plus_plus_int @ ( times_times_int @ ( minus_minus_int @ A_9 @ B_9 ) @ E_1 ) @ C_9 ) @ D_3 ) ) )).

thf(fact_58_le__add__iff2,axiom,(
    ! [A_8: int,E: int,C_8: int,B_8: int,D_2: int] :
      ( ( ord_less_eq_int @ ( plus_plus_int @ ( times_times_int @ A_8 @ E ) @ C_8 ) @ ( plus_plus_int @ ( times_times_int @ B_8 @ E ) @ D_2 ) )
    <=> ( ord_less_eq_int @ C_8 @ ( plus_plus_int @ ( times_times_int @ ( minus_minus_int @ B_8 @ A_8 ) @ E ) @ D_2 ) ) ) )).

thf(fact_59_zadd__left__mono,axiom,(
    ! [K: int,I: int,J: int] :
      ( ( ord_less_eq_int @ I @ J )
     => ( ord_less_eq_int @ ( plus_plus_int @ K @ I ) @ ( plus_plus_int @ K @ J ) ) ) )).

thf(fact_60_diff__eq__diff__less__eq,axiom,(
    ! [A_7: int,B_7: int,C_7: int,D_1: int] :
      ( ( ( minus_minus_int @ A_7 @ B_7 )
        = ( minus_minus_int @ C_7 @ D_1 ) )
     => ( ( ord_less_eq_int @ A_7 @ B_7 )
      <=> ( ord_less_eq_int @ C_7 @ D_1 ) ) ) )).

thf(fact_61_add__le__imp__le__left,axiom,(
    ! [C_6: int,A_6: int,B_6: int] :
      ( ( ord_less_eq_int @ ( plus_plus_int @ C_6 @ A_6 ) @ ( plus_plus_int @ C_6 @ B_6 ) )
     => ( ord_less_eq_int @ A_6 @ B_6 ) ) )).

thf(fact_62_add__le__imp__le__right,axiom,(
    ! [A_5: int,C_5: int,B_5: int] :
      ( ( ord_less_eq_int @ ( plus_plus_int @ A_5 @ C_5 ) @ ( plus_plus_int @ B_5 @ C_5 ) )
     => ( ord_less_eq_int @ A_5 @ B_5 ) ) )).

thf(fact_63_add__mono,axiom,(
    ! [C_4: int,D: int,A_4: int,B_4: int] :
      ( ( ord_less_eq_int @ A_4 @ B_4 )
     => ( ( ord_less_eq_int @ C_4 @ D )
       => ( ord_less_eq_int @ ( plus_plus_int @ A_4 @ C_4 ) @ ( plus_plus_int @ B_4 @ D ) ) ) ) )).

thf(fact_64_add__left__mono,axiom,(
    ! [C_3: int,A_3: int,B_3: int] :
      ( ( ord_less_eq_int @ A_3 @ B_3 )
     => ( ord_less_eq_int @ ( plus_plus_int @ C_3 @ A_3 ) @ ( plus_plus_int @ C_3 @ B_3 ) ) ) )).

thf(fact_65_add__right__mono,axiom,(
    ! [C_2: int,A_2: int,B_2: int] :
      ( ( ord_less_eq_int @ A_2 @ B_2 )
     => ( ord_less_eq_int @ ( plus_plus_int @ A_2 @ C_2 ) @ ( plus_plus_int @ B_2 @ C_2 ) ) ) )).

thf(fact_66_add__le__cancel__left,axiom,(
    ! [C_1: int,A_1: int,B_1: int] :
      ( ( ord_less_eq_int @ ( plus_plus_int @ C_1 @ A_1 ) @ ( plus_plus_int @ C_1 @ B_1 ) )
    <=> ( ord_less_eq_int @ A_1 @ B_1 ) ) )).

thf(fact_67_add__le__cancel__right,axiom,(
    ! [A: int,C: int,B: int] :
      ( ( ord_less_eq_int @ ( plus_plus_int @ A @ C ) @ ( plus_plus_int @ B @ C ) )
    <=> ( ord_less_eq_int @ A @ B ) ) )).

thf(fact_68_order__refl,axiom,(
    ! [X_1: int] :
      ( ord_less_eq_int @ X_1 @ X_1 ) )).

thf(fact_69_linorder__le__cases,axiom,(
    ! [X: int,Y: int] :
      ( ~ ( ord_less_eq_int @ X @ Y )
     => ( ord_less_eq_int @ Y @ X ) ) )).

thf(fact_70_zle__refl,axiom,(
    ! [W: int] :
      ( ord_less_eq_int @ W @ W ) )).

thf(fact_71_zle__linear,axiom,(
    ! [Z: int,W: int] :
      ( ( ord_less_eq_int @ Z @ W )
      | ( ord_less_eq_int @ W @ Z ) ) )).

thf(fact_72_zle__trans,axiom,(
    ! [K: int,I: int,J: int] :
      ( ( ord_less_eq_int @ I @ J )
     => ( ( ord_less_eq_int @ J @ K )
       => ( ord_less_eq_int @ I @ K ) ) ) )).

thf(fact_73_zle__antisym,axiom,(
    ! [Z: int,W: int] :
      ( ( ord_less_eq_int @ Z @ W )
     => ( ( ord_less_eq_int @ W @ Z )
       => ( Z = W ) ) ) )).

%----Conjectures (1)
thf(conj_0,conjecture,
    ( ( times_times_int @ ( twoSqu1535104286sum2sq @ ( product_Pair_int_int @ a @ b ) ) @ ( twoSqu1535104286sum2sq @ ( product_Pair_int_int @ p @ q ) ) )
    = ( twoSqu1535104286sum2sq @ ( product_Pair_int_int @ ( plus_plus_int @ ( times_times_int @ a @ p ) @ ( times_times_int @ b @ q ) ) @ ( minus_minus_int @ ( times_times_int @ a @ q ) @ ( times_times_int @ b @ p ) ) ) ) )).

%------------------------------------------------------------------------------