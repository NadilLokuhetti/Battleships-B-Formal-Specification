/* BattleshipsGame
 * Author: User1
 * Creation date: 12/9/2024
 */
MACHINE
    BattleshipsGame
SETS
    PLAYER = {player1, player2};
    REPORT = {FLEET_DEPLOYED, CANNOT_DEPLOY_FLEET, HIT, MISS, INVALID_TARGET, 
              PLAYER_1_WINS, PLAYER_2_WINS, GAME_ONGOING, AWAITING_DEPLOYMENT,ALREADY_SHOT};
    GAME_STATUS = {deploying, ongoing, finished}
    
DEFINITIONS
    ANIMATION_FUNCTION == ({ row, col, img | row:(1..GRID_SIZE) & col: (1..(GRID_SIZE*2)+1) & img=1 });
    ANIMATION_FUNCTION1 == ({ row, col, img | row:(1..GRID_SIZE) & col: (1..(GRID_SIZE*2)+1) & img=2 & col = 11 });
    ANIMATION_FUNCTION2 == ({ row, col, img | row:(1..GRID_SIZE) & col:(1..(GRID_SIZE*2)+1) & img=3 & (col,11-row) : player1_ships });
    ANIMATION_FUNCTION3 == ({ row, col, img | row:(1..GRID_SIZE) & col:(1..(GRID_SIZE*2)+1) & img=4 & (col-11,11-row) : player2_ships });
    ANIMATION_FUNCTION4 == ({ row, col, img | row:(1..GRID_SIZE) & col:(1..(GRID_SIZE*2)+1) & img=5 & (col,11-row) : player1_hits });
    ANIMATION_FUNCTION5 == ({ row, col, img | row:(1..GRID_SIZE) & col:(1..(GRID_SIZE*2)+1) & img=5 & (col-11,11-row) : player2_hits });
    

/* Images for animations */
    ANIMATION_IMG1 == "images/square.png";
    ANIMATION_IMG2 == "images/col11.png";  
    ANIMATION_IMG3 == "images/ship.png";
    ANIMATION_IMG4 == "images/player2_ship.png";
    ANIMATION_IMG5 == "images/hit.png";

CONSTANTS
    GRID_SIZE,   /* Size of the grid */
    FLEET_SIZE,  /* Number of ships in the fleet */
    GRID         /* Set of all grid positions */

PROPERTIES
    GRID_SIZE = 10 &
    FLEET_SIZE = 3 &
    GRID = (1..GRID_SIZE) * (1..GRID_SIZE)

VARIABLES
    player1_ships,    /* Set of positions of player 1's ships */
    player2_ships,    /* Set of positions of player 2's ships */
    current_player,   /* Which player's turn it is */
    game_state,       /* Current state of the game */
    player1_shots,    /* Number of shots taken by player 1 */
    player2_shots,    /* Number of shots taken by player 2 */
    player1_hits,     /* Number of hits taken by player 1 */
    player2_hits      /* Number of hits taken by player 2 */

INVARIANT
    player1_ships <: GRID &    /*Creating a subset from the grid*/
    player2_ships <: GRID &
    card(player1_ships) <= FLEET_SIZE &    /*Checking the player ships are = to Fleet size*/
    card(player2_ships) <= FLEET_SIZE &
    current_player : PLAYER &    /*Current player turn*/
    game_state : GAME_STATUS &    /*Valid game status*/
    player1_shots : NAT & 
    player2_shots : NAT &
    player1_hits <: GRID &
    player2_hits <: GRID 

INITIALISATION
    player1_ships := {} ||
    player2_ships := {} ||
    current_player := player1 ||    /*Starting from player 1*/
    game_state := deploying ||    /*Game begins from deploying state*/
    player1_shots := 0 ||
    player2_shots := 0 ||
    player1_hits := {} ||
    player2_hits := {}

OPERATIONS
    report <-- deployFleet(player, positions) =
    PRE
        player : PLAYER & 
        current_player = player & 
        positions <: GRID & 
        card(positions) = FLEET_SIZE & 
        game_state = deploying & 
        report : REPORT
    THEN
        IF card(player1_ships) = FLEET_SIZE & card(player2_ships) = FLEET_SIZE 
        THEN
            game_state := ongoing
        ELSE   
            IF player = player1 THEN
                player1_ships := player1_ships <+ positions ||    /*Deploying the ships to the player 1 set*/
                report := FLEET_DEPLOYED ||
                current_player := player2    /*Changing the player*/
            ELSIF player = player2  THEN
                player2_ships := player2_ships <+ positions ||    /*Deploying the ships to the player 2 set*/
                report := FLEET_DEPLOYED ||
                current_player := player1 ||    /*Changing the player*/
                game_state := ongoing
            ELSE
                report := CANNOT_DEPLOY_FLEET
            END
        END
    END;


    /* Player Shoots Operation */
    report <-- playerShoots(target) =
    PRE
        target : GRID &
        game_state = ongoing &
        report : REPORT
    THEN
        IF game_state /= ongoing THEN
            report := INVALID_TARGET
        ELSIF current_player = player1 THEN
            player1_shots := player1_shots + 1 ||    /*Increasing the shot count*/
            player2_hits := player2_hits \/ {target}||    /*Adding the player 2 hits*/
            IF target : player2_ships THEN
                player2_ships := player2_ships - {target} ||    /*removing the ship from the fleet*/
                IF (player2_ships - {target} = {}) THEN
                    game_state := finished ||
                    report := PLAYER_1_WINS
                ELSE
                    report := HIT
                END ||
                current_player := player2
            ELSIF(target:player2_hits) THEN
                report := ALREADY_SHOT
            ELSE
                report := MISS ||
                current_player := player2
            END
        ELSE
            player2_shots := player2_shots + 1 ||    /*Increasing the shot count*/
            player1_hits :=  player1_hits \/ {target}||    /*Adding the player 2 hits*/
            IF target : player1_ships THEN
                player1_ships := player1_ships - {target} ||     /*removing the ship from the fleet*/
                IF (player1_ships - {target} = {}) THEN
                    game_state := finished ||
                    report := PLAYER_2_WINS
                ELSE
                    report := HIT
                END ||
                current_player := player1
            ELSIF(target:player1_hits) THEN
                report := ALREADY_SHOT
            ELSE
                report := MISS ||
                current_player := player1
            END
        END
    END;

    /* ship Location Operations */
    shipsquares <-- shipLocations(player) =
    PRE
        player : PLAYER
    THEN
        IF player = player1 THEN
            shipsquares := player1_ships    /*Displaying the player ship locations*/
        ELSE
            shipsquares := player2_ships
        END
    END;
    
    /*Ship count operation*/
    shipCounts <-- shipsLeft =
    BEGIN
        shipCounts := card(player1_ships) |-> card(player2_ships) /*Fleet count as (3|->3))*/
    END;
    
    /*Shot count operation*/
    shotCount <-- shotsTaken(player) =    /*Players shot count*/
    PRE
        player : PLAYER
    THEN
        IF player = player1 THEN
            shotCount := player1_shots
        ELSE
            shotCount := player2_shots
        END
    END;
    
    /*Game status operation*/
    report <-- gameStatus =
    BEGIN
        IF game_state = deploying THEN
            IF player1_ships = {} & player2_ships = {} THEN
                report := AWAITING_DEPLOYMENT    /*Till players deploying*/
            ELSIF player2_ships = {} THEN
                report := AWAITING_DEPLOYMENT
            END
        ELSIF game_state = ongoing THEN
            report := GAME_ONGOING    /*ongoing since players have deployed the ships*/
        ELSIF card(player2_ships) = 0 THEN    /*Displaying the winner*/
            report := PLAYER_1_WINS
        ELSE
            report := PLAYER_2_WINS
        END
    END

END

